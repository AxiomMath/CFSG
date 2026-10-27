module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem

section Inputs


@[expose] def GGSecFiveJNormDInput'
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ c ∈ Subgroup.centralizer (D : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J

end Inputs

section Pure

theorem s2jn_ne_one_of_isReflection {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {Bs : Subgroup G} {r : MulAut ↥Bs}
    (hr : GGIsReflection p r) : r ≠ 1 := by
  intro h1
  have hcard := hr.2
  rw [h1] at hcard
  have hfix : Nat.card {b : ↥Bs // (1 : MulAut ↥Bs) b = b} = Nat.card ↥Bs :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)
  rw [hfix] at hcard
  have hpos' : 0 < Nat.card ↥Bs := Nat.card_pos
  have : Nat.card ↥Bs * 1 < Nat.card ↥Bs * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hpos'
  omega

theorem s2jn_refl_pair_eq_or_transvection {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (Es : Subgroup ↥Bs) (hEs : IsCyclic Es)
    {r₁ r₂ : MulAut ↥Bs} (h₁ : r₁ * r₁ = 1) (h₂ : r₂ * r₂ = 1) (n₁ : r₁ ≠ 1) (n₂ : r₂ ≠ 1)
    (hE₁ : ∀ b, b⁻¹ * r₁ b ∈ Es) (hE₂ : ∀ b, b⁻¹ * r₂ b ∈ Es) :
    r₁ * r₂ = 1 ∨ GGIsTransvection p (r₁ * r₂) := by
  haveI : IsMulCommutative Bs := hBs.1
  haveI := Fact.mk hp
  have hpow : ∀ a : ↥Bs, a ^ p = 1 := fun a => Subtype.ext (by simpa using hBs.2 a a.2)
  have hrr : ∀ r : MulAut ↥Bs, r * r = 1 → ∀ b, r (r b) = b := fun r h b => by
    have := congrArg (fun f : MulAut ↥Bs => f b) h
    simpa using this
  have hmov : ∀ r : MulAut ↥Bs, r ≠ 1 → ∃ b, r b ≠ b := fun r hr => by
    by_contra h
    push Not at h
    exact hr (MulEquiv.ext fun b => by simpa using h b)
  obtain ⟨b₁, hb₁⟩ := hmov r₁ n₁
  have hu₁ : b₁⁻¹ * r₁ b₁ ≠ 1 := fun h => hb₁ (inv_mul_eq_one.mp h).symm
  have hEcard : Nat.card Es = p := by
    obtain ⟨g, hg⟩ := hEs.exists_generator
    have hord : orderOf g = Nat.card Es := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hpow g)
    have hg1 : g ≠ 1 := by
      intro h
      have := hg ⟨b₁⁻¹ * r₁ b₁, hE₁ b₁⟩
      rw [h] at this
      obtain ⟨k, hk⟩ := this
      apply hu₁
      have := congrArg Subtype.val hk
      simpa using this.symm
    rw [← hord]
    exact orderOf_eq_prime hgp hg1
  have key : ∀ r : MulAut ↥Bs, r * r = 1 → r ≠ 1 → (∀ b, b⁻¹ * r b ∈ Es) →
      ∀ e ∈ Es, r e = e⁻¹ := by
    intro r hr hr1 hE e he
    obtain ⟨b, hb⟩ := hmov r hr1
    have hu : b⁻¹ * r b ≠ 1 := fun h => hb (inv_mul_eq_one.mp h).symm
    have hru : r (b⁻¹ * r b) = (b⁻¹ * r b)⁻¹ := by
      rw [map_mul, map_inv, hrr r hr b]
      simp [mul_comm]
    have hz : Subgroup.zpowers (b⁻¹ * r b) = Es := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]; exact hE b
      · rw [hEcard, Nat.card_zpowers]
        have : orderOf (b⁻¹ * r b) = p := orderOf_eq_prime (hpow _) hu
        omega
    rw [← hz] at he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    rw [map_zpow, hru, inv_zpow]
  have k₁ := key r₁ h₁ n₁ hE₁
  have k₂ := key r₂ h₂ n₂ hE₂
  set φ : MulAut ↥Bs := r₁ * r₂ with hφ
  have hν : ∀ b, b⁻¹ * φ b = (b⁻¹ * r₁ b) * (b⁻¹ * r₂ b)⁻¹ := by
    intro b
    have e2 : r₂ b = b * (b⁻¹ * r₂ b) := by simp
    have : φ b = r₁ b * (b⁻¹ * r₂ b)⁻¹ := by
      rw [hφ, MulAut.mul_apply]
      conv_lhs => rw [e2]
      rw [map_mul, k₁ _ (hE₂ b)]
    rw [this]
    simp [mul_assoc, mul_comm, mul_left_comm]
  have hνE : ∀ b, b⁻¹ * φ b ∈ Es := fun b => by
    rw [hν]; exact Es.mul_mem (hE₁ b) (Es.inv_mem (hE₂ b))
  have hφE : ∀ b, φ (b⁻¹ * φ b) = b⁻¹ * φ b := fun b => by
    have hm := hνE b
    rw [hφ, MulAut.mul_apply, k₂ _ hm, map_inv, k₁ _ hm, inv_inv]
  by_cases hφ1 : φ = 1
  · exact Or.inl hφ1
  right
  refine ⟨?_, hφE⟩
  obtain ⟨b₀, hb₀⟩ := hmov φ hφ1
  let ν : ↥Bs →* ↥Bs := MonoidHom.mk' (fun b => b⁻¹ * φ b) (fun a b => by
    simp only [mul_inv_rev, map_mul]
    ac_rfl)
  have hker : Nat.card {b : ↥Bs // φ b = b} = Nat.card ν.ker := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun b => by
      rw [MonoidHom.mem_ker]
      change φ b = b ↔ b⁻¹ * φ b = 1
      rw [inv_mul_eq_one, eq_comm]
  have hrange_le : ν.range ≤ Es := by
    rintro _ ⟨b, rfl⟩
    exact hνE b
  have hrange : Nat.card ν.range = p := by
    have hd : Nat.card ν.range ∣ Nat.card Es := Subgroup.card_dvd_of_le hrange_le
    rw [hEcard] at hd
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exfalso
      have hbot : ν.range = ⊥ := Subgroup.eq_bot_of_card_eq _ h
      apply hb₀
      have : ν b₀ ∈ ν.range := ⟨b₀, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      change b₀⁻¹ * φ b₀ = 1 at this
      rw [inv_mul_eq_one] at this
      exact this.symm
    · exact h
  have h := Subgroup.card_mul_index ν.ker
  rw [Subgroup.index_ker] at h
  rw [hker, ← hrange]
  exact h

theorem s2jn_comm_mem_of_mem_ggAutomizer {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer L Bs)
    (b : ↥Bs) : b⁻¹ * r b ∈ L.subgroupOf Bs := by
  obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp hr
  rw [Subgroup.mem_subgroupOf]
  have hb : (b⁻¹ : G) ∈ Subgroup.normalizer (L : Set G) := by
    have := hN (Subgroup.inv_mem _ b.2)
    exact this
  have h1 : (b⁻¹ : G) * g * (b⁻¹ : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hb g).mp hgL
  have h2 : (((b⁻¹ * r b : ↥Bs)) : G) = ((b⁻¹ : G) * g * (b⁻¹ : G)⁻¹) * g⁻¹ := by
    rw [Subgroup.coe_mul, hg b]
    simp [mul_assoc]
  rw [h2]
  exact L.mul_mem h1 (L.inv_mem hgL)

theorem s2jn_not_isCyclic_of_two_refl {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs L : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hNT : GGNoTransvection p Bs) {r₁ r₂ : MulAut ↥Bs} (h₁A : r₁ ∈ ggAutomizer L Bs)
    (h₂A : r₂ ∈ ggAutomizer L Bs) (h₁ : GGIsReflection p r₁) (h₂ : GGIsReflection p r₂)
    (hne : r₁ ≠ r₂) : ¬ IsCyclic ↥(L.subgroupOf Bs) := by
  intro hcyc
  have h := s2jn_refl_pair_eq_or_transvection hp hp2 hBs _ hcyc
    (by simpa [sq] using h₁.1) (by simpa [sq] using h₂.1)
    (s2jn_ne_one_of_isReflection hp h₁) (s2jn_ne_one_of_isReflection hp h₂)
    (s2jn_comm_mem_of_mem_ggAutomizer hN h₁A) (s2jn_comm_mem_of_mem_ggAutomizer hN h₂A)
  rcases h with h | h
  · apply hne
    have h22 : r₂ * r₂ = 1 := by simpa [sq] using h₂.1
    calc r₁ = r₁ * (r₂ * r₂) := by rw [h22, mul_one]
      _ = (r₁ * r₂) * r₂ := by rw [mul_assoc]
      _ = r₂ := by rw [h, one_mul]
  · obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp (Subgroup.mul_mem _ h₁A h₂A)
    exact hNT _ ⟨g, Subgroup.mem_top g, hgN, hg⟩ h

open CFSG.LocalAnalysis.ComponentInitial in
theorem s2jn_mem_normalizer_of_not_cyclic {G : Type} [Group G] [Finite G]
    {p : ℕ} {x c : G} {L Bs : Subgroup G}
    (hLc : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    (hBs : IsElemAbelian p Bs) (hnc : ¬ IsCyclic ↥(L.subgroupOf Bs))
    (hcx : c ∈ Subgroup.centralizer ({x} : Set G)) :
    c ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcx' : c * x * c⁻¹ = x := by
    have := (Subgroup.mem_centralizer_iff.mp hcx) x rfl
    rw [← this]; group
  have hcomp : CFSG.Assembly.IsComponentOf (L.map (MulAut.conj c).toMonoidHom)
      (Subgroup.centralizer ({x} : Set G)) := by
    have := isComponentOf_map_conj hLc c
    rwa [map_conj_centralizer_singleton, hcx'] at this
  rcases isComponentOf_eq_or_commute hLc hcomp with h | h
  · exact h.symm
  · exfalso
    apply hnc
    have hle : L.map (MulAut.conj c).toMonoidHom ≤ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.commutator_comm] at h
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    set Es := L.subgroupOf Bs with hEs
    set S : Subgroup G := (Es.map Bs.subtype).map (MulAut.conj c).toMonoidHom with hS
    have hSL : S ≤ L.map (MulAut.conj c).toMonoidHom := by
      apply Subgroup.map_mono
      rintro _ ⟨k, hk, rfl⟩
      exact hk
    have hSp : ∀ s ∈ S, s ^ p = 1 := by
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have h1 : ((k : ↥Bs) : G) ^ p = 1 := by simpa using hBs.2 _ k.2
      change ((MulAut.conj c).toMonoidHom (Bs.subtype k)) ^ p = 1
      rw [← map_pow]
      change (MulAut.conj c).toMonoidHom (((k : ↥Bs) : G) ^ p) = 1
      rw [h1, map_one]
    have hpg : IsPGroup p S := fun g =>
      ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hSp g g.2)⟩
    have hSc : IsCyclic S := hcyc S (hSL.trans hle) hpg
    let e : Es ≃* S :=
      (Es.equivMapOfInjective Bs.subtype Bs.subtype_injective).trans
        ((Es.map Bs.subtype).equivMapOfInjective (MulAut.conj c).toMonoidHom
          (MulAut.conj c).injective)
    exact e.isCyclic.mpr hSc

open CFSG.LocalAnalysis.ComponentInitial in
theorem s2jn_layer_conj_mem {G : Type} [Group G] [Finite G]
    {D L J : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (D : Set G)) (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hJ : J = CFSG.Assembly.LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G))) :
    ∀ j ∈ J, c * j * c⁻¹ ∈ J := by
  set M : Subgroup G := L ⊓ Subgroup.centralizer (D : Set G) with hMdef
  have hcM : c ∈ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hL' := (Subgroup.mem_normalizer_iff.mp hcL) y
    have hD' : y ∈ Subgroup.centralizer (D : Set G) ↔
        c * y * c⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
      constructor
      · intro hy
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hy) (Subgroup.inv_mem _ hc)
      · intro hy
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hy) hc
        simpa [mul_assoc] using this
    rw [hMdef, Subgroup.mem_inf, Subgroup.mem_inf, hL', hD']
  have hM : M.map (MulAut.conj c).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hcM
  have hmap : J.map (MulAut.conj c).toMonoidHom ≤ J := by
    rw [Subgroup.map_le_iff_le_comap]
    nth_rewrite 1 [hJ]
    apply sSup_le
    intro K hK
    rw [← Subgroup.map_le_iff_le_comap]
    have hK' := isComponentOf_map_conj hK c
    rw [hM] at hK'
    rw [hJ]
    exact le_sSup hK'
  intro j hj
  exact hmap (Subgroup.mem_map_of_mem _ hj)

end Pure

section Main

theorem s2jn_exists_two_refl_of_tableBPos {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs X : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hrk : 2 ≤ (ggU t n f).D.rank) (hpos : GGTableBPos p Bs X t n f ψ) :
    ∃ r₁ r₂ : MulAut ↥Bs, r₁ ∈ ggAutomizer X Bs ∧ r₂ ∈ ggAutomizer X Bs ∧
      GGIsReflection p r₁ ∧ GGIsReflection p r₂ ∧ r₁ ≠ r₂ := by
  obtain ⟨ε, hεrefl, -, -⟩ := hpos
  let M := coxeterMatrix (ggU t n f).D.isFiniteType
  let i₁ : Fin (ggU t n f).D.rank := ⟨0, by omega⟩
  let i₂ : Fin (ggU t n f).D.rank := ⟨1, by omega⟩
  have hne : i₁ ≠ i₂ := fun h => by
    have := congrArg Fin.val h
    simp [i₁, i₂] at this
  refine ⟨((ε (M.simple i₁) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs),
    ((ε (M.simple i₂) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs), (ε (M.simple i₁)).2,
    (ε (M.simple i₂)).2, hεrefl i₁, hεrefl i₂, fun h => ?_⟩
  have h1 : ε (M.simple i₁) = ε (M.simple i₂) := Subtype.ext h
  have h2 : M.simple i₁ = M.simple i₂ := ε.injective h1
  have h3 : M.toCoxeterSystem.simple i₁ = M.toCoxeterSystem.simple i₂ := by
    rw [CoxeterMatrix.toCoxeterSystem_simple]; exact h2
  exact hne (M.toCoxeterSystem.simple_injective h3)

theorem s2jn_ggSecFiveJNormDInput'_holds
    : GGSecFiveJNormDInput' := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL c hc j hj
  obtain ⟨t, n, f, ψ, hloc, -, hTB⟩ := s2jn_exists_tableBFrame G p B Bs x L D J 𝒦 hcfg hL
  have hC : GGConfig p B Bs x L D J := hcfg.1.1
  have hS : LargeEvenSStar p B x L := hcfg.1.1.1.2.2.2.2.2.2.1
  have hLc : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hS.2.2.2.2
  have hDx : x ∈ D := hC.2.2.1.2.2.2.1
  have hJL : J = CFSG.Assembly.LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hC.2.2.1.2.2.2.2.1
  have hcx : c ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]
      exact (Subgroup.mem_centralizer_iff.mp hc) x hDx
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨⟨hp, hp2, hadm, h3t⟩, -, ⟨hBs, hBsN, -⟩, -⟩ := hloc
  have hrk : 2 ≤ (ggU t n f).D.rank := two_le_lieUniversal_rank t n 2 f Nat.prime_two hadm h3t
  obtain ⟨r₁, r₂, h₁A, h₂A, h₁, h₂, hne⟩ := s2jn_exists_two_refl_of_tableBPos hrk hTB
  have hnc := s2jn_not_isCyclic_of_two_refl hp hp2 hBs hBsN hNT h₁A h₂A h₁ h₂ hne
  have hcL := s2jn_mem_normalizer_of_not_cyclic hLc hcyc hBs hnc hcx
  exact s2jn_layer_conj_mem hc hcL hJL j hj


theorem ggSecFiveJNormInput'_holds
    : GGSecFiveJNormInput' := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hBstar : GGBstar p B Bs := hconf.2.1
  have hstdsub : LargeEvenStdSub p B x L D J := hconf.2.2
  have hstdpre : LargeEvenStdSubPre p B x L D J := hstdsub.1
  refine ⟨hstdpre.2.2.2.2.2.1.1.trans inf_le_left, fun c hc j hj => ?_⟩
  have hD_le_Bs : D ≤ Bs := hstdpre.1.trans hBstar.1
  exact s2jn_ggSecFiveJNormDInput'_holds G p B Bs x L D J 𝒦 hcfg hsplit c
    (Subgroup.centralizer_le hD_le_Bs hc) j hj

end Main

end CFSG.StandardType
