module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardRes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

private theorem s16c11_v1_center_perm_three_eq_bot :
    Subgroup.center (Equiv.Perm (Fin 3)) = ⊥ := by
  have key : ∀ g : Equiv.Perm (Fin 3), (∀ h, h * g = g * h) → g = 1 := by
    decide +kernel
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_center_iff] at hg
  rw [Subgroup.mem_bot]
  exact key g hg

private theorem s16c11_v1_fixV_prod_map {W : Type} [CommGroup W] {J₀ : Subgroup W}
    {L : Subgroup (MulAut W)} (φ : ↥L →* MulAut ↥J₀) (Θ : ↥J₀ × ↥J₀ ≃* W)
    (hΘ : ∀ (l : ↥L) (p : ↥J₀ × ↥J₀), (l : MulAut W) (Θ p) = Θ (φ l p.1, φ l p.2))
    (B : Subgroup (MulAut W)) (hB : B ≤ L) :
    fixV B = ((fixV ((B.subgroupOf L).map φ)).prod
      (fixV ((B.subgroupOf L).map φ))).map (Θ : ↥J₀ × ↥J₀ →* W) := by
  ext w
  constructor
  · intro hw
    have hcoord : ∀ b : MulAut ↥J₀, b ∈ (B.subgroupOf L).map φ →
        b (Θ.symm w).1 = (Θ.symm w).1 ∧ b (Θ.symm w).2 = (Θ.symm w).2 := by
      intro b hb
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hb
      have hfix := mem_fixV.mp hw (l : MulAut W) (Subgroup.mem_subgroupOf.mp hl)
      have hp : Θ.symm w = (φ l (Θ.symm w).1, φ l (Θ.symm w).2) := by
        apply Θ.injective
        rw [MulEquiv.apply_symm_apply, ← hΘ l (Θ.symm w), MulEquiv.apply_symm_apply, hfix]
      exact ⟨(congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩
    refine Subgroup.mem_map.mpr ⟨Θ.symm w, Subgroup.mem_prod.mpr ⟨?_, ?_⟩,
      Θ.apply_symm_apply w⟩
    · exact mem_fixV.mpr fun b hb => (hcoord b hb).1
    · exact mem_fixV.mpr fun b hb => (hcoord b hb).2
  · intro hw
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hw
    refine mem_fixV.mpr ?_
    intro b hb
    have hp1 : p.1 ∈ fixV ((B.subgroupOf L).map φ) := (Subgroup.mem_prod.mp hp).1
    have hp2 : p.2 ∈ fixV ((B.subgroupOf L).map φ) := (Subgroup.mem_prod.mp hp).2
    have hmem : φ ⟨b, hB hb⟩ ∈ (B.subgroupOf L).map φ :=
      Subgroup.mem_map.mpr ⟨⟨b, hB hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have h1 : φ ⟨b, hB hb⟩ p.1 = p.1 := mem_fixV.mp hp1 _ hmem
    have h2 : φ ⟨b, hB hb⟩ p.2 = p.2 := mem_fixV.mp hp2 _ hmem
    change ((⟨b, hB hb⟩ : ↥L) : MulAut W) (Θ p) = Θ p
    rw [hΘ ⟨b, hB hb⟩ p, h1, h2]

theorem s16c11_v1_exists_B_alt (c : ℕ) {W : Type} [CommGroup W] [Finite W]
    {X K L : Subgroup (MulAut W)} {J₀ : Subgroup W} (hM : S16C11Model X K J₀) (hLX : L ≤ X)
    (hLK : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l) (hJ : ∀ l ∈ L, ∀ j ∈ J₀, l j ∈ J₀)
    {E : Subgroup (MulAut ↥J₀)}
    (hEL : E ≤ (CFSG.Quasithin.H13.VolI.resHom L J₀ hJ).range)
    (hE3 : IsPGroup 3 ↥E) (hEnc : ¬ IsCyclic ↥E) (hcard : Nat.card ↥(fixV E) = 2 ^ c) :
    ∃ B : Subgroup (MulAut W), B ≤ L ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B ∧
      Nat.card ↥(fixV B) = 2 ^ (2 * c) := by
  classical
  obtain ⟨hJ', Θ, hΘ⟩ := s16c11_v1_model_pair hM hLX hLK
  have hJeq : hJ = hJ' := Subsingleton.elim _ _
  rw [← hJeq] at hΘ
  let φ : ↥L →* MulAut ↥J₀ := CFSG.Quasithin.H13.VolI.resHom L J₀ hJ
  have hinj : Function.Injective φ := s16c11_v1_resHom_injective hM hLX hLK hJ
  let B : Subgroup (MulAut W) := (E.comap φ).map L.subtype
  have hBle : B ≤ L := Subgroup.map_subtype_le (E.comap φ)
  have hBp : IsPGroup 3 ↥B := (hE3.comap_of_injective φ hinj).map L.subtype
  have hEncB : ¬ IsCyclic ↥B := by
    have eE' : (E.comap φ) ≃* E :=
      (MulEquiv.ofBijective (φ.subgroupMap (E.comap φ))
        ⟨φ.subgroupMap_injective (E.comap φ) hinj,
          φ.subgroupMap_surjective (E.comap φ)⟩).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hEL))
    have eB : (E.comap φ) ≃* B :=
      Subgroup.equivMapOfInjective (E.comap φ) L.subtype L.subtype_injective
    intro hcyc
    exact hEnc ((eE'.symm.trans eB).isCyclic.mpr hcyc)
  have hfixB : Nat.card ↥(fixV B) = 2 ^ (2 * c) := by
    have hBsub : (B.subgroupOf L).map φ = E := by
      have h1 : B.subgroupOf L = E.comap φ := by
        show B.comap L.subtype = E.comap φ
        rw [show B = (E.comap φ).map L.subtype from rfl,
          Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
      rw [h1]
      exact Subgroup.map_comap_eq_self hEL
    have hfix : fixV B = ((fixV E).prod (fixV E)).map (Θ : ↥J₀ × ↥J₀ →* W) := by
      rw [← hBsub]
      exact s16c11_v1_fixV_prod_map φ Θ hΘ B hBle
    rw [hfix, Subgroup.card_map_of_injective (f := (Θ : ↥J₀ × ↥J₀ →* W)) Θ.injective,
      Nat.card_congr (Subgroup.prodEquiv (fixV E) (fixV E)).toEquiv, Nat.card_prod, hcard,
      ← pow_add, show c + c = 2 * c by ring]
  exact ⟨B, hBle, hBp, hEncB, hfixB⟩

theorem s16c11_v1_le_right_of_centralizes {A : Type} [Group A] {K L₀ X L : Subgroup A}
    (hK : IsSym ↥K 3) (hdir : IsInternalDirect K L₀ X) (hLX : L ≤ X)
    (hLK : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l) : L ≤ L₀ := by
  obtain ⟨hcomm, hdisj, hsup⟩ := hdir
  have hKc : K ≤ Subgroup.centralizer (L₀ : Set A) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hnorm : K ≤ Subgroup.normalizer (L₀ : Set A) :=
    hKc.trans (Subgroup.centralizer_le_normalizer _)
  have hZ : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1 := by
    intro k hk hkcent
    obtain ⟨e⟩ := hK
    have hke : e ⟨k, hk⟩ ∈ Subgroup.center (Equiv.Perm (Fin 3)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k', rfl⟩ := e.surjective g
      have hc : (⟨k, hk⟩ : ↥K) * k' = k' * ⟨k, hk⟩ := by
        apply Subtype.ext
        simpa using hkcent k' k'.2
      calc e k' * e ⟨k, hk⟩ = e (k' * ⟨k, hk⟩) := (map_mul e k' ⟨k, hk⟩).symm
        _ = e (⟨k, hk⟩ * k') := by rw [hc]
        _ = e ⟨k, hk⟩ * e k' := map_mul e ⟨k, hk⟩ k'
    have h1 : e ⟨k, hk⟩ = 1 := by
      rw [s16c11_v1_center_perm_three_eq_bot] at hke
      exact Subgroup.mem_bot.1 hke
    have h2 : (⟨k, hk⟩ : ↥K) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  intro x hx
  have hxs : x ∈ (↑(K ⊔ L₀) : Set A) := by
    rw [hsup]
    exact hLX hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K L₀ hnorm] at hxs
  obtain ⟨k, hk, l, hl, rfl⟩ := hxs
  have hk1 : k = 1 := hZ k hk fun k' hk' => by
    have h1 : (k * l) * k' = k' * (k * l) := hLK (k * l) hx k' hk'
    have h2 : l * k' = k' * l := (Subgroup.mem_centralizer_iff.1 (hKc hk')) l hl
    have h4 : k * k' * l = k' * k * l := by
      calc k * k' * l = k * (k' * l) := by group
        _ = k * (l * k') := by rw [← h2]
        _ = (k * l) * k' := by group
        _ = k' * (k * l) := h1
        _ = k' * k * l := by group
    exact mul_right_cancel h4
  simpa [hk1] using hl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
