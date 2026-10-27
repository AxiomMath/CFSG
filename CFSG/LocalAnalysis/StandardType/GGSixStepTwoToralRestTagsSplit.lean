module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralRestTagsWeyl
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType

namespace StepTwoSplit

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Adj

@[expose] def GGExcSplitWeylAdjAt (τ : Tag) (K : Type) [Field K] (p : ℕ) : Prop :=
  Nat.Coprime p (Nat.card (ggAutomizer ⊤ (TableBExc.torusPow τ K p))) ∧
    ∀ v ∈ TableBExc.torusPow τ K p, v ≠ 1 → ∀ L : Subgroup (adjointGroup τ K),
      IsComponentOf L (Subgroup.centralizer {v}) →
        TableBExc.torusPow τ K p ≤ Subgroup.normalizer (L : Set (adjointGroup τ K)) ∧
          ∃ Q : Subgroup (adjointGroup τ K), Q ≤ L ∧
            Q ≤ Subgroup.normalizer (TableBExc.torusPow τ K p : Set (adjointGroup τ K)) ∧
              TableBExc.torusPow τ K p ⊓ Subgroup.centralizer (Q : Set (adjointGroup τ K)) ≤
                Subgroup.centralizer (L : Set (adjointGroup τ K))

theorem commute_of_mem_torusPow {τ : Tag} {K : Type} [Field K] {p : ℕ}
    {a b : adjointGroup τ K} (ha : a ∈ TableBExc.torusPow τ K p)
    (hb : b ∈ TableBExc.torusPow τ K p) : a * b = b * a :=
  Subtype.ext (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ha.1)
    (torusGroup_le_diagonalGroup hb.1))

end Adj

section Transport

variable {C G : Type} [Group C] [Group G] {ψ : C →* G}

theorem map_le_normalizer_map {H V : Subgroup C} (h : V ≤ Subgroup.normalizer (H : Set C))
    (ψ : C →* G) :
    V.map ψ ≤ Subgroup.normalizer ((H.map ψ : Subgroup G) : Set G) :=
  (Subgroup.map_mono h).trans (Subgroup.le_normalizer_map ψ)

theorem map_le_centralizer_map {H V : Subgroup C} (h : V ≤ Subgroup.centralizer (H : Set C))
    (ψ : C →* G) : V.map ψ ≤ Subgroup.centralizer ((H.map ψ : Subgroup G) : Set G) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨h', hh', rfl⟩
  rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (h hv)) h' hh']

theorem map_centralizer_singleton (hψ : Function.Injective ψ) (c : C) :
    (Subgroup.centralizer {c}).map ψ = ψ.range ⊓ Subgroup.centralizer {ψ c} := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hu]
  · rintro ⟨⟨u, rfl⟩, hy⟩
    refine ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr (hψ ?_), rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hy

theorem splitWeyl_of_map {p : ℕ} (hψ : Function.Injective ψ) {V : Subgroup C} {Bs : Subgroup G}
    (hBs : Bs = V.map ψ) (hA : Nat.Coprime p (Nat.card (ggAutomizer ⊤ V)))
    (hcomp : ∀ v ∈ V, v ≠ 1 → ∀ L : Subgroup C, IsComponentOf L (Subgroup.centralizer {v}) →
      V ≤ Subgroup.normalizer (L : Set C) ∧ ∃ Q : Subgroup C, Q ≤ L ∧
        Q ≤ Subgroup.normalizer (V : Set C) ∧
          V ⊓ Subgroup.centralizer (Q : Set C) ≤ Subgroup.centralizer (L : Set C)) :
    Nat.Coprime p (Nat.card (ggAutomizer ψ.range Bs)) ∧
      ∀ b ∈ Bs, b ≠ 1 → ∀ L₁ : Subgroup G, IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}) →
        Bs ≤ Subgroup.normalizer (L₁ : Set G) ∧ ∃ Q : Subgroup G, Q ≤ L₁ ∧
          Q ≤ Subgroup.normalizer (Bs : Set G) ∧
            Bs ⊓ Subgroup.centralizer (Q : Set G) ≤ Subgroup.centralizer (L₁ : Set G) := by
  subst hBs
  set e : V ≃* ↥(V.map ψ) := V.equivMapOfInjective ψ hψ with he
  have he_apply : ∀ v : V, ((e v : ↥(V.map ψ)) : G) = ψ v := fun _ => rfl
  refine ⟨?_, ?_⟩
  ·
    have hle : ggAutomizer ψ.range (V.map ψ) ≤
        (ggAutomizer ⊤ V).map (MulAut.congr e).toMonoidHom := by
      intro φ hφ
      obtain ⟨x, ⟨c, rfl⟩, hxN, hx⟩ := mem_ggAutomizer_iff.mp hφ
      have hcN : c ∈ Subgroup.normalizer (V : Set C) := by
        rw [Subgroup.mem_normalizer_iff]
        intro v
        constructor
        · intro hv
          obtain ⟨w, hw, hwv⟩ := (Subgroup.mem_normalizer_iff.mp hxN (ψ v)).mp ⟨v, hv, rfl⟩
          rw [← map_inv, ← map_mul, ← map_mul] at hwv
          exact (hψ hwv) ▸ hw
        · intro hv
          obtain ⟨w, hw, hwv⟩ := (Subgroup.mem_normalizer_iff.mp hxN (ψ v)).mpr
            ⟨c * v * c⁻¹, hv, by rw [map_mul, map_mul, map_inv]⟩
          exact (hψ hwv) ▸ hw
      refine ⟨ggConjAut V hcN, ggConjAut_mem_ggAutomizer (Subgroup.mem_top c) hcN, ?_⟩
      ext w
      obtain ⟨v, rfl⟩ := e.surjective w
      change ((e (ggConjAut V hcN (e.symm (e v))) : ↥(V.map ψ)) : G) = _
      rw [MulEquiv.symm_apply_apply, he_apply, ggConjAut_apply, hx, he_apply, map_mul, map_mul,
        map_inv]
    have hcard : Nat.card ((ggAutomizer ⊤ V).map (MulAut.congr e).toMonoidHom) =
        Nat.card (ggAutomizer ⊤ V) :=
      Subgroup.card_map_of_injective (MulAut.congr e).injective
    exact Nat.Coprime.coprime_dvd_right ((Subgroup.card_dvd_of_le hle).trans hcard.dvd) hA
  · rintro _ ⟨v, hv, rfl⟩ hb1 L₁ hL₁
    have hv1 : v ≠ 1 := fun h => hb1 (by rw [h, map_one])
    have hL₁le : L₁ ≤ ψ.range := hL₁.1.trans inf_le_left
    have hL₁eq : (L₁.comap ψ).map ψ = L₁ := Subgroup.map_comap_eq_self hL₁le
    have hL' : IsComponentOf (L₁.comap ψ) (Subgroup.centralizer {v}) := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hψ, hL₁eq,
        map_centralizer_singleton hψ]
      exact hL₁
    obtain ⟨hVN, Q, hQL, hQN, hQC⟩ := hcomp v hv hv1 _ hL'
    refine ⟨hL₁eq ▸ map_le_normalizer_map hVN ψ, Q.map ψ, hL₁eq ▸ Subgroup.map_mono hQL,
      map_le_normalizer_map hQN ψ, ?_⟩
    rintro _ ⟨⟨w, hw, rfl⟩, hwC⟩
    have hw' : w ∈ V ⊓ Subgroup.centralizer (Q : Set C) := by
      refine ⟨hw, Subgroup.mem_centralizer_iff.mpr fun q hq => hψ ?_⟩
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hwC (ψ q) ⟨q, hq, rfl⟩
    rw [← hL₁eq]
    exact map_le_centralizer_map (le_refl _) ψ ⟨w, hQC hw', rfl⟩

end Transport

section Conj

theorem splitWeyl_of_adjAt {τ : Tag} {K : Type} [Field K] [Finite K] {G : Type} [Group G]
    {p : ℕ} (hp : p.Prime) {B Bs G₀ : Subgroup G} {ψ : adjointGroup τ K →* G}
    (hψ : Function.Injective ψ) (hrange₀ : ψ.range = G₀) (hBs : GGBstar p B Bs) (hBsψ : Bs ≤ G₀)
    (hidx : ¬ p ∣ ((torusGroup τ K).subgroupOf (adjointGroup τ K)).index)
    (hadj : GGExcSplitWeylAdjAt τ K p) :
    Nat.Coprime p (Nat.card (ggAutomizer G₀ Bs)) ∧
      ∀ b ∈ Bs, b ≠ 1 → ∀ L₁ : Subgroup G, IsComponentOf L₁ (G₀ ⊓ Subgroup.centralizer {b}) →
        Bs ≤ Subgroup.normalizer (L₁ : Set G) ∧ ∃ Q : Subgroup G, Q ≤ L₁ ∧
          Q ≤ Subgroup.normalizer (Bs : Set G) ∧
            Bs ⊓ Subgroup.centralizer (Q : Set G) ≤ Subgroup.centralizer (L₁ : Set G) := by
  subst hrange₀
  have hV' : IsElemAbelian p (Bs.comap ψ) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hψ ?_)⟩⟩, fun y hy => hψ ?_⟩
    · change ψ ((a : adjointGroup τ K) * b) = ψ ((b : adjointGroup τ K) * a)
      rw [map_mul, map_mul]
      have := hBs.2.1.1
      exact congrArg Subtype.val (mul_comm' (⟨ψ a, a.2⟩ : Bs) ⟨ψ b, b.2⟩)
    · rw [map_pow, hBs.2.1.2 _ hy, map_one]
  obtain ⟨g, hg⟩ := TableBExc.exists_conj_le_torusPow hp hidx hV'
  set ψ' : adjointGroup τ K →* G := ψ.comp (MulAut.conj g⁻¹).toMonoidHom with hψ'
  have hψ'apply : ∀ c, ψ' c = ψ (g⁻¹ * c * g) := fun c => by
    simp [hψ']
  have hψ'inj : Function.Injective ψ' := hψ.comp (MulAut.conj g⁻¹).injective
  have hrange : ψ'.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨_, (hψ'apply c).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨g * c * g⁻¹, by rw [hψ'apply]; group⟩
  have hle1 : Bs ≤ (TableBExc.torusPow τ K p).map ψ' := by
    intro b hb
    obtain ⟨u, rfl⟩ := hBsψ hb
    have hu : u ∈ Bs.comap ψ := hb
    refine ⟨g * u * g⁻¹, hg ⟨u, hu, rfl⟩, ?_⟩
    rw [hψ'apply]
    group
  have hBsEq : Bs = (TableBExc.torusPow τ K p).map ψ' := by
    refine le_antisymm hle1 ?_
    rintro _ ⟨t, ht, rfl⟩
    refine hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_) (by
      rw [← map_pow, ht.2, map_one])
    obtain ⟨t', ht', rfl⟩ := hle1 hb
    rw [← map_mul, ← map_mul, commute_of_mem_torusPow ht' ht]
  rw [← hrange]
  exact splitWeyl_of_map hψ'inj hBsEq hadj.1 hadj.2

end Conj

end StepTwoSplit

section Inputs

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley StepTwoSplit

@[expose] def GGExcSplitWeylF4Input : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → 5 ≤ p →
    p ∣ Nat.card K - 1 → GGExcSplitWeylAdjAt .F4 K p

@[expose] def GGExcSplitWeylE8Input : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → 11 ≤ p →
    p ∣ Nat.card K - 1 → GGExcSplitWeylAdjAt .E8 K p

theorem five_le_of_not_dvd_weylF4 {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ 1152) : 5 ≤ p := by
  by_contra hlt
  have h2 := hp.two_le
  interval_cases p
  · exact h (by norm_num)
  · exact h (by norm_num)
  · exact absurd hp (by norm_num)

theorem eleven_le_of_not_dvd_weylE8 {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ 696729600) : 11 ≤ p := by
  by_contra hlt
  have h2 := hp.two_le
  interval_cases p
  · exact h (by norm_num)
  · exact h (by norm_num)
  · exact absurd hp (by norm_num)
  · exact h (by norm_num)
  · exact absurd hp (by norm_num)
  · exact h (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)

end Inputs

section Tags

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley StepTwoSplit

theorem ggStepTwoExcSplitWeylOn_F4_of_adj (h : GGExcSplitWeylF4Input) :
    GGStepTwoExcSplitWeylOn .F4 := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hW hq
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hp5 : 5 ≤ p := five_le_of_not_dvd_weylF4 hp hW
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpq : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hq
  let ψ₀ : adjointGroup .F4 (GaloisField 2 f) →* G := ψ
  have hrange : ψ₀.range = ggG0 p B x L D J := hctx.2.2.2.2.1.1
  have hker : ψ₀.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) := hctx.2.2.2.2.1.2
  have hψ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).le
  have hC : Subgroup.centralizer (ψ₀.range : Set G) = ⊥ := by rw [hrange]; exact s1.1
  have hBsψ : Bs ≤ ggG0 p B x L D J := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := PsiDiag.Adj.exists_mem_centralizer_F4 (K := GaloisField 2 f) ψ₀ hker
      (hctx.2.2.2.2.2.2.1.2 b hb)
    rw [hC, Subgroup.mem_bot] at hbg
    rw [eq_inv_of_mul_eq_one_left hbg, ← hrange]
    exact inv_mem hg
  obtain ⟨hA, hcomp⟩ := splitWeyl_of_adjAt (τ := .F4) (K := GaloisField 2 f) hp hψ hrange
    hctx.2.1 hBsψ (TableBF4.not_dvd_index_torusGroup hp hp5 hpq) (h (GaloisField 2 f) p hp hp5 hpq)
  exact ⟨hA, fun b L₁ hpair => hcomp b hpair.1 hpair.2.1 L₁ hpair.2.2.1⟩

theorem ggStepTwoExcSplitWeylOn_E8_of_adj (h : GGExcSplitWeylE8Input) :
    GGStepTwoExcSplitWeylOn .E8 := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hW hq
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hp11 : 11 ≤ p := eleven_le_of_not_dvd_weylE8 hp hW
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpq : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hq
  let ψ₀ : adjointGroup .E8 (GaloisField 2 f) →* G := ψ
  have hrange : ψ₀.range = ggG0 p B x L D J := hctx.2.2.2.2.1.1
  have hker : ψ₀.ker ≤ Subgroup.center (adjointGroup .E8 (GaloisField 2 f)) := hctx.2.2.2.2.1.2
  have hψ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).le
  have hC : Subgroup.centralizer (ψ₀.range : Set G) = ⊥ := by rw [hrange]; exact s1.1
  have hBsψ : Bs ≤ ggG0 p B x L D J := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := PsiDiag.Adj.exists_mem_centralizer_E8 (K := GaloisField 2 f) ψ₀ hker
      (hctx.2.2.2.2.2.2.1.2 b hb)
    rw [hC, Subgroup.mem_bot] at hbg
    rw [eq_inv_of_mul_eq_one_left hbg, ← hrange]
    exact inv_mem hg
  obtain ⟨hA, hcomp⟩ := splitWeyl_of_adjAt (τ := .E8) (K := GaloisField 2 f) hp hψ hrange
    hctx.2.1 hBsψ (TableBExc.not_dvd_index_torusGroup_E8 hp hp11 hpq)
    (h (GaloisField 2 f) p hp hp11 hpq)
  exact ⟨hA, fun b L₁ hpair => hcomp b hpair.1 hpair.2.1 L₁ hpair.2.2.1⟩

end Tags

end CFSG.StandardType
