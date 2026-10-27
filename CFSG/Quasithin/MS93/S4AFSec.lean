module

public import CFSG.Quasithin.MS93.S4AFMod

public section

namespace CFSG.Quasithin.MS93.S4A.F

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S46 CFSG.Assembly.LowTwoRank
open scoped Matrix commutatorElement

section Quot

variable {G : Type} [Group G] {K V Z : Subgroup G}

theorem exists_quotient_conj (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hZV : Z ≤ V)
    (hKZ : K ≤ Subgroup.normalizer (Z : Set G)) (hVc : ∀ v ∈ V, ∀ w ∈ V, ⁅v, w⁆ ∈ Z) :
    ∃ (X : Type) (_ : CommGroup X) (π : ↥V →* X) (ρ : ↥K →* MulAut X),
      Function.Surjective π ∧ (∀ v : ↥V, π v = 1 ↔ (v : G) ∈ Z) ∧
      ∀ (k : ↥K) (v : ↥V), ρ k (π v) = π (conjOn hKV k v) := by
  have hN : (Z.subgroupOf V).Normal := ⟨fun z hz v => by
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    have h := hVc v v.2 z (hZV hz)
    have he : ((v * z * v⁻¹ : ↥V) : G) = ⁅(v : G), (z : G)⁆ * z := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [he]
    exact Z.mul_mem h hz⟩
  let Xq := ↥V ⧸ Z.subgroupOf V
  let _ : CommGroup Xq :=
    { (QuotientGroup.Quotient.group (Z.subgroupOf V)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
              Subgroup.mem_subgroupOf]
            have h := hVc _ (V.inv_mem b.2) _ (V.inv_mem a.2)
            have he : (((a * b)⁻¹ * (b * a) : ↥V) : G) =
                ⁅((b : G))⁻¹, ((a : G))⁻¹⁆ := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
              group
            rw [he]
            exact h }
  have hmap : ∀ k : ↥K,
      (Z.subgroupOf V).map (conjOn hKV k : ↥V →* ↥V) = Z.subgroupOf V := by
    intro k
    have hle : ∀ k : ↥K,
        (Z.subgroupOf V).map (conjOn hKV k : ↥V →* ↥V) ≤ Z.subgroupOf V := by
      rintro k _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hz
      rw [Subgroup.mem_subgroupOf]
      show ((conjOn hKV k z : ↥V) : G) ∈ Z
      rw [coe_conjOn_apply]
      exact (Subgroup.mem_normalizer_iff.mp (hKZ k.2) z).mp hz
    refine le_antisymm (hle k) fun z hz => ?_
    refine ⟨conjOn hKV k⁻¹ z, ?_, ?_⟩
    · exact hle k⁻¹ ⟨z, hz, rfl⟩
    · change conjOn hKV k (conjOn hKV k⁻¹ z) = z
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  let act : ↥K →* MulAut Xq :=
    { toFun := fun k => QuotientGroup.congr (Z.subgroupOf V) (Z.subgroupOf V)
        (conjOn hKV k) (hmap k)
      map_one' := by
        ext q
        induction q using QuotientGroup.induction_on with
        | H v =>
          simp only [QuotientGroup.congr_mk, map_one, MulAut.one_apply]
      map_mul' := fun k k' => by
        ext q
        induction q using QuotientGroup.induction_on with
        | H v =>
          simp only [QuotientGroup.congr_mk, map_mul, MulAut.mul_apply] }
  refine ⟨Xq, inferInstance, QuotientGroup.mk' (Z.subgroupOf V), act,
    QuotientGroup.mk'_surjective _, fun v => ?_, fun k v => rfl⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

end Quot

section Pre

variable {G : Type} [Group G] {V Z : Subgroup G} {X : Type} [CommGroup X] (π : ↥V →* X)

@[expose] def pre (S : Subgroup X) : Subgroup G := (S.comap π).map V.subtype

variable {π}

theorem mem_pre {S : Subgroup X} {g : G} : g ∈ pre π S ↔ ∃ hg : g ∈ V, π ⟨g, hg⟩ ∈ S := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem pre_le (S : Subgroup X) : pre π S ≤ V := Subgroup.map_subtype_le _

theorem pre_mono {S S' : Subgroup X} (h : S ≤ S') : pre π S ≤ pre π S' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

variable (hker : ∀ v : ↥V, π v = 1 ↔ (v : G) ∈ Z) (hZV : Z ≤ V)
include hker hZV

theorem le_pre (S : Subgroup X) : Z ≤ pre π S := fun z hz =>
  mem_pre.mpr ⟨hZV hz, by rw [(hker ⟨z, hZV hz⟩).mpr hz]; exact S.one_mem⟩

theorem pre_bot : pre π ⊥ = Z := by
  refine le_antisymm (fun g hg => ?_) (le_pre hker hZV ⊥)
  obtain ⟨hgV, h1⟩ := mem_pre.mp hg
  exact (hker ⟨g, hgV⟩).mp (Subgroup.mem_bot.mp h1)

omit hker hZV in
theorem pre_top : pre π ⊤ = V := by
  ext g
  rw [mem_pre]
  exact ⟨fun ⟨hg, _⟩ => hg, fun hg => ⟨hg, Subgroup.mem_top _⟩⟩

omit hker hZV in
theorem pre_inf (S S' : Subgroup X) : pre π (S ⊓ S') = pre π S ⊓ pre π S' := by
  ext g
  simp only [Subgroup.mem_inf, mem_pre]
  constructor
  · rintro ⟨hg, h1, h2⟩
    exact ⟨⟨hg, h1⟩, ⟨hg, h2⟩⟩
  · rintro ⟨⟨hg, h1⟩, ⟨_, h2⟩⟩
    exact ⟨hg, h1, h2⟩

omit hker hZV in
theorem pre_sup (hπ : Function.Surjective π) (S S' : Subgroup X) :
    pre π (S ⊔ S') = pre π S ⊔ pre π S' := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgV, hgS⟩ := mem_pre.mp hg
    obtain ⟨s₁, hs₁, s₂, hs₂, hs⟩ := Subgroup.mem_sup.mp hgS
    obtain ⟨w₁, rfl⟩ := hπ s₁
    have h1 : (w₁ : G) ∈ pre π S := mem_pre.mpr ⟨w₁.2, hs₁⟩
    have h2 : (w₁ : G)⁻¹ * g ∈ pre π S' := by
      refine mem_pre.mpr ⟨V.mul_mem (V.inv_mem w₁.2) hgV, ?_⟩
      have e : π ⟨(w₁ : G)⁻¹ * g, V.mul_mem (V.inv_mem w₁.2) hgV⟩ = (π w₁)⁻¹ * π ⟨g, hgV⟩ := by
        rw [← map_inv, ← map_mul]
        rfl
      rw [e, ← hs, inv_mul_cancel_left]
      exact hs₂
    have e : g = (w₁ : G) * ((w₁ : G)⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  · exact sup_le (pre_mono le_sup_left) (pre_mono le_sup_right)

theorem card_pre [Finite ↥V] (hπ : Function.Surjective π) (S : Subgroup X) :
    Z.relIndex (pre π S) = Nat.card S := by
  have : Finite ↥Z := Finite.of_injective _ (Subgroup.inclusion_injective hZV)
  have h1 := Subgroup.relIndex_mul_card Z (pre π S)
  rw [inf_eq_left.mpr (le_pre hker hZV S)] at h1
  have h2 : Nat.card ↥(pre π S) = Nat.card S * Nat.card Z := by
    have h3 := B1More.card_map_mul_card_inf_ker (S.comap π) π
    rw [Subgroup.map_comap_eq_self_of_surjective hπ] at h3
    have h4 : (S.comap π) ⊓ π.ker = Z.subgroupOf V := by
      ext v
      rw [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_subgroupOf,
        hker]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rw [(hker v).mpr h]
        exact S.one_mem
    rw [h4, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv] at h3
    rw [pre, Subgroup.card_map_of_injective V.subtype_injective, ← h3]
  have hZ0 : 0 < Nat.card Z := Nat.card_pos
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hZ0 h1

end Pre

section Act

variable {G : Type} [Group G] {K V Z : Subgroup G} {X : Type} [CommGroup X] {π : ↥V →* X}
  {hKV : K ≤ Subgroup.normalizer (V : Set G)} {ρ : ↥K →* MulAut X}
  (hρ : ∀ (k : ↥K) (v : ↥V), ρ k (π v) = π (conjOn hKV k v))

omit [CommGroup X] in
theorem commutatorElement_mem_V (hKV : K ≤ Subgroup.normalizer (V : Set G)) {v : G} (hv : v ∈ V)
    {k : G} (hk : k ∈ K) : ⁅v, k⁆ ∈ V := by
  have h1 : k * v⁻¹ * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hKV hk) _).mp (V.inv_mem hv)
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc k]
  exact V.mul_mem hv h1

include hρ in
theorem pi_commutatorElement {v : G} (hv : v ∈ V) {k : G} (hk : k ∈ K) :
    π ⟨⁅v, k⁆, commutatorElement_mem_V hKV hv hk⟩ = (ρ ⟨k, hk⟩ (π ⟨v, hv⟩) * (π ⟨v, hv⟩)⁻¹)⁻¹ := by
  rw [hρ, mul_inv_rev, inv_inv, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn_apply, commutatorElement_def]
  group

variable (hker : ∀ v : ↥V, π v = 1 ↔ (v : G) ∈ Z) (hZV : Z ≤ V)

include hker in
theorem pre_map {R : Subgroup G} (hZR : Z ≤ R) (hRV : R ≤ V) :
    pre π ((R.subgroupOf V).map π) = R := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgV, w, hw, hwg⟩ := mem_pre.mp hg
    have h1 : π (w⁻¹ * ⟨g, hgV⟩) = 1 := by rw [map_mul, map_inv, hwg, inv_mul_cancel]
    have h2 : (w : G)⁻¹ * g ∈ R := hZR ((hker _).mp h1)
    have e : g = (w : G) * ((w : G)⁻¹ * g) := by group
    rw [e]
    exact R.mul_mem (Subgroup.mem_subgroupOf.mp hw) h2
  · intro r hr
    exact mem_pre.mpr ⟨hRV hr, ⟨r, hRV hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩

include hρ hker hZV in
theorem pre_commV (hπ : Function.Surjective π) {A : Subgroup G} (hAK : A ≤ K) :
    pre π (commV ((A.subgroupOf K).map ρ)) = ⁅V, A⁆ ⊔ Z := by
  have hVA : ⁅V, A⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv a ha
    exact commutatorElement_mem_V hKV hv (hAK ha)
  apply le_antisymm
  · rw [← pre_map hker (le_sup_right : Z ≤ ⁅V, A⁆ ⊔ Z) (sup_le hVA hZV)]
    refine pre_mono ?_
    rw [G6.commV_le_iff]
    rintro _ ⟨⟨k, hkK⟩, hk, rfl⟩ y
    obtain ⟨⟨v, hv⟩, rfl⟩ := hπ y
    have h1 := pi_commutatorElement hρ hv hkK
    refine ⟨⟨⁅v, k⁆, commutatorElement_mem_V hKV hv hkK⟩⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      rw [Subgroup.coe_inv]
      exact Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hv
        (Subgroup.mem_subgroupOf.mp hk)))
    · rw [map_inv, h1, inv_inv]
  · refine sup_le ?_ (le_pre hker hZV _)
    rw [Subgroup.commutator_le]
    intro v hv a ha
    refine mem_pre.mpr ⟨commutatorElement_mem_V hKV hv (hAK ha), ?_⟩
    rw [pi_commutatorElement hρ hv (hAK ha)]
    exact Subgroup.inv_mem _ (G6.mem_commV_of_mem (X := (A.subgroupOf K).map ρ)
      (x := ρ ⟨a, hAK ha⟩) (Subgroup.mem_map.mpr ⟨⟨a, hAK ha⟩, Subgroup.mem_subgroupOf.mpr ha,
        rfl⟩) _)

include hρ in
theorem commutator_pre_le_of_fix {C S : Subgroup X}
    (hC : ∀ (k : ↥K), ∀ c ∈ C, ρ k c * c⁻¹ ∈ S) : ⁅pre π C, K⁆ ≤ pre π S := by
  rw [Subgroup.commutator_le]
  intro c hc k hk
  obtain ⟨hcV, hcC⟩ := mem_pre.mp hc
  refine mem_pre.mpr ⟨commutatorElement_mem_V hKV hcV hk, ?_⟩
  rw [pi_commutatorElement hρ hcV hk]
  exact S.inv_mem (hC ⟨k, hk⟩ _ hcC)

include hρ hker in
theorem commutator_pre_le_of_centralize {L : Subgroup G} (hLK : L ≤ K) {S : Subgroup X}
    (hS : ∀ l : ↥K, (l : G) ∈ L → ∀ x ∈ S, ρ l x = x) : ⁅pre π S, L⁆ ≤ Z := by
  rw [Subgroup.commutator_le]
  intro w hw l hl
  obtain ⟨hwV, hwS⟩ := mem_pre.mp hw
  refine (hker ⟨_, commutatorElement_mem_V hKV hwV (hLK hl)⟩).mp ?_
  rw [pi_commutatorElement hρ hwV (hLK hl), hS ⟨l, hLK hl⟩ hl _ hwS, mul_inv_cancel, inv_one]

include hρ in
theorem isSumOfNaturalModulesVia_pre (hπ : Function.Surjective π) {P S : Subgroup X}
    (hP : ∀ (k : ↥K), ∀ x ∈ P, ρ k x ∈ P) (hSP : S ≤ P) {F' : Type} [Field F']
    (τ : ↥K →* SL3 F') (β : ↥P →* Multiplicative (Fin 3 → F')) (hβs : Function.Surjective β)
    (hβk : ∀ p : ↥P, β p = 1 ↔ (p : X) ∈ S)
    (hβe : ∀ (k : ↥K) (p : ↥P), β (resRho ρ P hP k p) =
      Multiplicative.ofAdd ((τ k : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (β p))) :
    IsSumOfNaturalModulesVia K (pre π P) (pre π S)
      ((specialLinearGroupEquivStatedSL 3 F').toMonoidHom.comp τ) false 1 := by
  have hPV : ∀ g ∈ pre π P, g ∈ V := fun g hg => pre_le P hg
  have hpre : ∀ (k : ↥K) (g : G) (hg : g ∈ pre π P),
      (k : G) * g * (k : G)⁻¹ ∈ pre π P := by
    intro k g hg
    obtain ⟨hgV, hgP⟩ := mem_pre.mp hg
    have hkg : (k : G) * g * (k : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hKV k.2) g).mp hgV
    refine mem_pre.mpr ⟨hkg, ?_⟩
    have e : π ⟨(k : G) * g * (k : G)⁻¹, hkg⟩ = ρ k (π ⟨g, hgV⟩) := by
      rw [hρ]
      rfl
    rw [e]
    exact hP k _ hgP
  have hnorm : K ≤ Subgroup.normalizer (pre π P : Set G) := by
    refine le_normalizer_of_map_conj_le fun k hk => ?_
    rintro _ ⟨g, hg, rfl⟩
    exact hpre ⟨k, hk⟩ g hg
  let j : ↥(pre π P) →* ↥P :=
    { toFun := fun g => ⟨π ⟨g, hPV g g.2⟩, (mem_pre.mp g.2).2⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun g g' => Subtype.ext (map_mul π ⟨g, hPV g g.2⟩ ⟨g', hPV g' g'.2⟩) }
  have hj : ∀ g, ((j g : ↥P) : X) = π ⟨g, hPV g g.2⟩ := fun _ => rfl
  have hjs : Function.Surjective j := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨v, hv⟩, rfl⟩ := hπ x
    exact ⟨⟨v, mem_pre.mpr ⟨hv, hx⟩⟩, rfl⟩
  refine ⟨hnorm, pre_mono hSP, (oneCoordEquiv (F := F')).symm.toMonoidHom.comp (β.comp j),
    (oneCoordEquiv (F := F')).symm.surjective.comp (hβs.comp hjs), ?_, ?_⟩
  · ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, MonoidHom.comp_apply, hβk, hj, mem_pre]
    exact ⟨fun h => ⟨hPV g g.2, h⟩, fun ⟨_, h⟩ => h⟩
  · intro a u v huv i
    have hjv : j v = resRho ρ P hP a (j u) := by
      apply Subtype.ext
      rw [hj, coe_resRho_apply, hj, hρ]
      congr 1
      exact Subtype.ext (by rw [coe_conjOn_apply]; exact huv)
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← toAdd_oneCoordEquiv, ← toAdd_oneCoordEquiv, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, hjv, hβe, toAdd_ofAdd]
    rfl

end Act

end CFSG.Quasithin.MS93.S4A.F
