module

public import CFSG.Quasithin.Vol2.Ch3B513NSp4L
public import CFSG.Quasithin.Vol2.Ch3B513NC1ii
public import CFSG.Quasithin.Background.B5FinSp
public import CFSG.Quasithin.Background.SmithB51G2DOff
public import CFSG.Quasithin.Vol2.Ch3B513NSpC

public section

namespace CFSG.Quasithin.B513N

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
open CFSG.Open (quasithinGenFitting)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem not_perfect_of_sp4_one {G : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥G)
    (h : BinaryNaturalSp4 G (commV G) (fixV G ⊓ commV G) 1) : False := by
  obtain ⟨π, hr⟩ := asSp4S6 W G (commV G) (fixV G ⊓ commV G) h
  have hinj := FFC.injective_of_faithful_sec (FFC.symDn_faithful (by norm_num)) hr
  let e : Equiv.Perm (Fin 6) ≃* ↥G := MulEquiv.ofBijective π ⟨hinj, hr.1⟩
  have : Group.IsPerfect (Equiv.Perm (Fin 6)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hsw : Equiv.swap (0 : Fin 6) 1 ∈ commutator (Equiv.Perm (Fin 6)) :=
    Group.IsPerfect.mem_commutator
  have h1 := Abelianization.commutator_subset_ker Equiv.Perm.sign hsw
  rw [MonoidHom.mem_ker, Equiv.Perm.sign_swap (by decide)] at h1
  exact absurd h1 (by decide)

theorem card_toSubgroup {A : Type*} [AddGroup A] (S : AddSubgroup A) :
    Nat.card ↥(AddSubgroup.toSubgroup S) = Nat.card ↥S :=
  Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, x.2⟩
      invFun := fun y => ⟨Multiplicative.ofAdd y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_comap_coord {U Z : Subgroup W} (hZU : Z ≤ U) {M : Type*} [CommGroup M]
    {β : ↥U →* M} (hβs : Function.Surjective β) (hβk : ∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z)
    (P : Subgroup M) : Nat.card (P.comap β) = Nat.card Z * Nat.card P := by
  rw [B5.G2D.card_comap_of_surjective hβs P]
  congr 1
  have : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hβk]
  rw [this]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv

theorem c1sp4_holds : C1Sp4 := by
  intro W _ _ hW G hne hB53 h1 hGL hU n hSp
  have hperf : Group.IsPerfect ↥G := by
    have := h1.1.1
    rwa [← hGL] at this
  rcases Nat.lt_or_ge n 2 with hn | hn
  · exfalso
    have hn1 : n = 1 := by
      obtain ⟨K, _, _, hK, -⟩ := hSp
      interval_cases n
      · have : 1 < Nat.card K := Finite.one_lt_card
        simp at hK
        omega
      · rfl
    subst hn1
    exact not_perfect_of_sp4_one hperf hSp
  obtain ⟨K, _, _, hK, π, hr⟩ := id hSp
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow hF
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hinv : ∀ x ∈ G, ∀ v ∈ commV G, x v ∈ commV G := fun x hx v hv => hU.2.1 ⟨x, hx⟩ v hv
  have hC : Nat.card ↥(fixV G ⊓ commV G) ≤ Nat.card K := by
    rw [hK]
    exact card_fixV_le_of_sp4 hW G (commV G) hinv hU.2.2.1 hn hK ⟨π, hr⟩
  have hCpos : 0 < Nat.card ↥(fixV G ⊓ commV G) := Nat.card_pos
  obtain ⟨β₀, hβs₀, hβk₀, hβe₀⟩ := FFModel.RealizesVia.coord rfl rfl hr
  let β : ↥(commV G) →* Multiplicative (Fin 2 ⊕ Fin 2 → K) := β₀
  have hβs : Function.Surjective β := hβs₀
  have hβk : ∀ u : ↥(commV G), β u = 1 ↔ (u : W) ∈ fixV G ⊓ commV G := hβk₀
  have hβe : ∀ (γ : ↥(StatedSp 2 K)) (u : ↥(commV G))
      (hu : ((π γ : ↥G) : MulAut W) (u : W) ∈ commV G),
      β ⟨((π γ : ↥G) : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd (spM γ *ᵥ Multiplicative.toAdd (β u)) := hβe₀
  have hπi : Function.Injective π := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hr
  have hUcard : Nat.card (commV G) = Nat.card ↥(fixV G ⊓ commV G) * Nat.card K ^ 4 := by
    rw [FFC.card_eq_of_realizes rfl hr]
    congr 1
    show Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K))) = _
    rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin 2 ⊕ Fin 2), Fintype.card_sum, Fintype.card_fin]
  obtain ⟨D, hD⟩ := exists_isFFStarMin hne hB53.2.1
  have hDG : D ≤ G := hD.1.1
  let φ : ↥(StatedSp 2 K) →* MulAut W := G.subtype.comp π
  have hφi : Function.Injective φ := fun a b h => hπi (Subtype.ext h)
  let D' : Subgroup ↥(StatedSp 2 K) := D.comap φ
  have hφr : φ.range = G := by
    show (G.subtype.comp π).range = G
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hr.1, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hD'map : D'.map φ = D := by
    rw [Subgroup.map_comap_eq, hφr]
    exact inf_eq_right.2 hDG
  have hD'card : Nat.card D' = Nat.card D := by
    rw [← hD'map, Subgroup.card_map_of_injective hφi]
  have hD'sur : ∀ d ∈ D, ∃ δ ∈ D', φ δ = d := fun d hd => by
    obtain ⟨δ, hδ⟩ := hr.1 ⟨d, hDG hd⟩
    have hφδ : φ δ = d := congrArg Subtype.val hδ
    exact ⟨δ, show φ δ ∈ D by rw [hφδ]; exact hd, hφδ⟩
  have hfin : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by simp
  obtain ⟨k, hk⟩ : ∃ k, Module.finrank K (fixSp D') = k := ⟨_, rfl⟩
  have hHcard : Nat.card (fixSp D') = Nat.card K ^ k := by
    rw [Module.natCard_eq_pow_finrank (K := K), hk]
  have hk3 : k ≤ 3 := by
    have hle := Submodule.finrank_le (fixSp D')
    rw [hfin, hk] at hle
    by_contra hk4
    have htop : fixSp D' = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hfin, hk]; omega)
    apply hD.1.2.1
    rw [← hD'map, eq_bot_of_fixSp_eq_top htop, Subgroup.map_bot]
  have hCUD : Nat.card ↥(fixV D ⊓ commV G) ≤ Nat.card ↥(fixV G ⊓ commV G) * Nat.card K ^ k := by
    have hle : (fixV D ⊓ commV G).subgroupOf (commV G) ≤
        (AddSubgroup.toSubgroup (fixSp D').toAddSubgroup).comap β := by
      intro u hu
      rw [Subgroup.mem_subgroupOf] at hu
      show Multiplicative.toAdd (β u) ∈ fixSp D'
      intro δ hδ
      have h1 := hβe δ u (hinv _ (π δ).2 u u.2)
      have h2 : (⟨((π δ : ↥G) : MulAut W) (u : W), hinv _ (π δ).2 u u.2⟩ : ↥(commV G)) = u :=
        Subtype.ext (hu.1 _ hδ)
      rw [h2] at h1
      exact (congrArg Multiplicative.toAdd h1).symm
    calc Nat.card ↥(fixV D ⊓ commV G)
        = Nat.card ↥((fixV D ⊓ commV G).subgroupOf (commV G)) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
      _ ≤ Nat.card ↥((AddSubgroup.toSubgroup (fixSp D').toAddSubgroup).comap β) :=
          Subgroup.card_le_of_le hle
      _ = Nat.card ↥(fixV G ⊓ commV G) * Nat.card K ^ k := by
          rw [card_comap_coord inf_le_right hβs hβk, card_toSubgroup, ← hHcard]
          rfl
  have hoff : Nat.card (commV G) ≤ Nat.card D * Nat.card ↥(fixV D ⊓ commV G) := by
    have h1 := Subgroup.relIndex_mul_card (fixV D) (commV G)
    have h2 := (relIndex_fixV_le_index D (commV G)).trans (index_fixV_le_card hD.1)
    rw [← h1]
    exact Nat.mul_le_mul_right _ h2
  have hmain : Nat.card K ^ 4 ≤ Nat.card D * Nat.card K ^ k := by
    have h1 : Nat.card ↥(fixV G ⊓ commV G) * Nat.card K ^ 4 ≤
        Nat.card ↥(fixV G ⊓ commV G) * (Nat.card D * Nat.card K ^ k) := by
      rw [← hUcard]
      calc Nat.card (commV G) ≤ Nat.card D * Nat.card ↥(fixV D ⊓ commV G) := hoff
        _ ≤ Nat.card D * (Nat.card ↥(fixV G ⊓ commV G) * Nat.card K ^ k) :=
            Nat.mul_le_mul_left _ hCUD
        _ = Nat.card ↥(fixV G ⊓ commV G) * (Nat.card D * Nat.card K ^ k) := by ring
    exact Nat.le_of_mul_le_mul_left h1 hCpos
  have hDk : Nat.card K ^ (4 - k) ≤ Nat.card D := by
    have h1 : Nat.card K ^ (4 - k) * Nat.card K ^ k ≤ Nat.card D * Nat.card K ^ k := by
      rw [← pow_add, show 4 - k + k = 4 by omega]
      exact hmain
    exact Nat.le_of_mul_le_mul_right h1 (pow_pos hq1 k)
  rcases Nat.lt_or_ge k 3 with hk2 | hk3'
  ·
    refine hasGood_of_offender_le hW hD (commV_mono hDG) ?_
    calc Nat.card ↥(fixV D ⊓ commV G) ≤ Nat.card ↥(fixV G ⊓ commV G) * Nat.card K ^ k := hCUD
      _ ≤ Nat.card K * Nat.card K ^ k := Nat.mul_le_mul_right _ hC
      _ = Nat.card K ^ (k + 1) := by ring
      _ ≤ Nat.card K ^ (2 * (4 - k)) := Nat.pow_le_pow_right hq1 (by omega)
      _ = (Nat.card K ^ (4 - k)) ^ 2 := by ring
      _ ≤ Nat.card D ^ 2 := Nat.pow_le_pow_left hDk 2
  ·
    have hk3e : k = 3 := le_antisymm hk3 hk3'
    subst hk3e
    have hDle : Nat.card D ≤ Nat.card K := hD'card ▸ card_le_of_finrank_fixSp_eq_three hk
    have hDq : Nat.card D = Nat.card K := le_antisymm hDle (by simpa using hDk)
    have hidx : (fixV D).index ≤ Nat.card K := (index_fixV_le_card hD.1).trans hDle
    have hrel : Nat.card K ≤ (fixV D).relIndex (commV G) := by
      have h1 := Subgroup.relIndex_mul_card (fixV D) (commV G)
      have h2 : Nat.card ↥(fixV G ⊓ commV G) * (Nat.card K * Nat.card K ^ 3) ≤
          Nat.card ↥(fixV G ⊓ commV G) * ((fixV D).relIndex (commV G) * Nat.card K ^ 3) := by
        calc Nat.card ↥(fixV G ⊓ commV G) * (Nat.card K * Nat.card K ^ 3)
            = Nat.card (commV G) := by rw [hUcard]; ring
          _ = (fixV D).relIndex (commV G) * Nat.card ↥(fixV D ⊓ commV G) := h1.symm
          _ ≤ (fixV D).relIndex (commV G) * (Nat.card ↥(fixV G ⊓ commV G) * Nat.card K ^ 3) :=
              Nat.mul_le_mul_left _ hCUD
          _ = Nat.card ↥(fixV G ⊓ commV G) * ((fixV D).relIndex (commV G) * Nat.card K ^ 3) := by
              ring
      exact Nat.le_of_mul_le_mul_right (Nat.le_of_mul_le_mul_left h2 hCpos) (pow_pos hq1 3)
    have hreleq : (fixV D).relIndex (commV G) = (fixV D).index :=
      le_antisymm (relIndex_fixV_le_index D (commV G)) (hidx.trans hrel)
    have hsup : commV G ⊔ fixV D = ⊤ := by
      have h1 : (fixV D).relIndex (commV G ⊔ fixV D) = (fixV D).relIndex (commV G) :=
        Subgroup.relIndex_sup_right (commV G) (fixV D)
      have h2 := Subgroup.relIndex_mul_index (le_sup_right : fixV D ≤ commV G ⊔ fixV D)
      rw [h1, hreleq] at h2
      have hpos : 0 < (fixV D).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have h3 : (commV G ⊔ fixV D).index = 1 := by
        have : (fixV D).index * (commV G ⊔ fixV D).index = (fixV D).index * 1 := by
          rw [h2, mul_one]
        exact Nat.eq_of_mul_eq_mul_left hpos this
      exact Subgroup.index_eq_one.1 h3
    have hP : Nat.card ↥((LieType.BorelTits.spForm 2 K).perp (fixSp D')) = Nat.card K := by
      have h1 := (LieType.BorelTits.spForm 2 K).finrank_perp (fixSp D')
      rw [hk, hfin] at h1
      rw [Module.natCard_eq_pow_finrank (K := K), show Module.finrank K
        ↥((LieType.BorelTits.spForm 2 K).perp (fixSp D')) = 1 by omega, pow_one]
    let Psub := AddSubgroup.toSubgroup
      ((LieType.BorelTits.spForm 2 K).perp (fixSp D')).toAddSubgroup
    let S : Subgroup W := (Psub.comap β).map (commV G).subtype
    have hS : commV D ≤ S := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨d, hd, w, rfl⟩
      have hw : w ∈ commV G ⊔ fixV D := by rw [hsup]; trivial
      obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
      obtain ⟨δ, hδ, rfl⟩ := hD'sur d hd
      have hdu : φ δ u ∈ commV G := hinv _ (π δ).2 u hu
      refine ⟨⟨φ δ u * u⁻¹, (commV G).mul_mem hdu ((commV G).inv_mem hu)⟩, ?_, ?_⟩
      · show β _ ∈ Psub
        have e1 : (⟨φ δ u * u⁻¹, (commV G).mul_mem hdu ((commV G).inv_mem hu)⟩ :
            ↥(commV G)) = ⟨φ δ u, hdu⟩ * (⟨u, hu⟩ : ↥(commV G))⁻¹ := rfl
        rw [e1, map_mul, map_inv]
        change β ⟨((π δ : ↥G) : MulAut W) ((⟨u, hu⟩ : ↥(commV G)) : W), hdu⟩ *
          (β ⟨u, hu⟩)⁻¹ ∈ Psub
        rw [hβe δ ⟨u, hu⟩ hdu]
        show spM δ *ᵥ Multiplicative.toAdd (β ⟨u, hu⟩) + -Multiplicative.toAdd (β ⟨u, hu⟩) ∈
          (LieType.BorelTits.spForm 2 K).perp (fixSp D')
        rw [← sub_eq_add_neg]
        exact sub_mem_perp hδ _
      · show φ δ u * u⁻¹ = φ δ (u * c) * (u * c)⁻¹
        rw [map_mul, hc _ hδ, _root_.mul_inv_rev, _root_.mul_assoc, ← _root_.mul_assoc c,
          mul_inv_cancel, one_mul]
    have hScard : Nat.card S ≤ Nat.card K * Nat.card K := by
      rw [Subgroup.card_map_of_injective (commV G).subtype_injective,
        card_comap_coord inf_le_right hβs hβk, card_toSubgroup]
      calc Nat.card ↥(fixV G ⊓ commV G) *
            Nat.card ↥((LieType.BorelTits.spForm 2 K).perp (fixSp D')).toAddSubgroup
          ≤ Nat.card K * Nat.card ↥((LieType.BorelTits.spForm 2 K).perp (fixSp D')) :=
            Nat.mul_le_mul_right _ hC
        _ = Nat.card K * Nat.card K := by rw [hP]
    refine hasGood_of_offender_le hW hD hS ?_
    calc Nat.card ↥(fixV D ⊓ S) ≤ Nat.card S := Subgroup.card_le_of_le inf_le_right
      _ ≤ Nat.card K * Nat.card K := hScard
      _ = Nat.card D ^ 2 := by rw [hDq]; ring

end CFSG.Quasithin.B513N
