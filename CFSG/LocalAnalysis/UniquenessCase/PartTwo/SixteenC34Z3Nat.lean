module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeNatural
public import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16c34_alternatingNatural_of_cyclic_three {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {K : Subgroup (MulAut W)} (hK : IsCyclicOrd ↥K 3)
    (hrk : rk ↥(commSub ⊤ K) = 2) : AlternatingNatural K (commSub ⊤ K) ⊥ 3 := by
  let U : Subgroup W := commSub ⊤ K
  have hK3 : Nat.card ↥K = 3 := hK.2
  have hrkU : rk ↥U = 2 := hrk
  have hodd : Odd (Nat.card ↥K) := by rw [hK3]; decide
  have hU4 : Nat.card ↥U = 4 := by
    rw [card_eq_two_pow hW U, hrkU]
    norm_num
  haveI hUnt : Nontrivial ↥U := by
    rw [← Finite.one_lt_card_iff_nontrivial, hU4]
    norm_num
  have hfix : fixV K ⊓ U = ⊥ := Asc81c.fixV_inf_commSub_eq_bot' hW hodd
  have hKle : K ≤ stabSub U := by
    intro k hk
    exact mem_stabSub_of_invariant
      (fun u hu => Asc81c.commSub_stable' hk hu)
      (fun u hu => Asc81c.commSub_stable' (K.inv_mem hk) hu)
  have hCentBot : K ⊓ centSub U = ⊥ := by
    by_contra hne
    have hdiv : Nat.card ↥(K ⊓ centSub U) ∣ Nat.card ↥K :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [hK3] at hdiv
    have hne1 : Nat.card ↥(K ⊓ centSub U) ≠ 1 := by
      intro h1
      exact hne (Subgroup.card_eq_one.mp h1)
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdiv with h1 | h3
    · exact hne1 h1
    · have hcard_le : Nat.card ↥K ≤ Nat.card ↥(K ⊓ centSub U) := by omega
      have hKeq : K ⊓ centSub U = K := Subgroup.eq_of_le_of_card_ge inf_le_left hcard_le
      have hKcent : K ≤ centSub U := hKeq ▸ inf_le_right
      have hUfix : U ≤ fixV K := by
        intro u hu
        rw [mem_fixV]
        intro x hx
        exact (mem_centSub.mp (hKcent hx)) u hu
      have hsub : U ≤ (⊥ : Subgroup W) := by
        calc U ≤ fixV K ⊓ U := le_inf hUfix le_rfl
          _ = ⊥ := hfix
      have hUbot : U = ⊥ := le_bot_iff.mp hsub
      rw [hUbot, Subgroup.card_bot] at hU4
      omega
  have hΓcard : Nat.card ↥(autSub K U) = 3 := by
    have h := card_autSub_mul (A := K) (U := U) hKle
    have hcent : Nat.card ↥(K ⊓ centSub U) = 1 := by rw [hCentBot, Subgroup.card_bot]
    rw [hcent, mul_one, hK3] at h
    exact h
  let ρ0 : ↥K →* ↥(autSub K U) :=
    (((resHom U).comp (Subgroup.inclusion hKle))).codRestrict (autSub K U) (fun k =>
      mem_autSub.mpr ⟨Subgroup.inclusion hKle k, by simpa using k.2, rfl⟩)
  have hρ0apply : ∀ k : ↥K, ((ρ0 k : ↥(autSub K U)) : MulAut ↥U) =
      resHom U ⟨(k : MulAut W), hKle k.2⟩ := fun _ => rfl
  have hsurj : Function.Surjective ρ0 := by
    intro φ
    obtain ⟨g, hgK, hgφ⟩ := mem_autSub.mp φ.2
    refine ⟨⟨(g : MulAut W), hgK⟩, ?_⟩
    apply Subtype.ext
    rw [hρ0apply]
    have hgg : (⟨((⟨(g : MulAut W), hgK⟩ : ↥K) : MulAut W),
        hKle (⟨(g : MulAut W), hgK⟩ : ↥K).2⟩ : ↥(stabSub U)) = g := Subtype.ext rfl
    rw [hgg]
    exact hgφ
  have hinj : Function.Injective ρ0 := by
    rw [← MonoidHom.ker_eq_bot_iff ρ0]
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hk
      have hres : resHom U ⟨(k : MulAut W), hKle k.2⟩ = 1 := by
        have h1 := hρ0apply k
        rw [hk] at h1
        simpa using h1.symm
      have hmem : (k : MulAut W) ∈ centSub U := by
        have h1 : ⟨(k : MulAut W), hKle k.2⟩ ∈ (resHom U).ker := by
          rw [MonoidHom.mem_ker]; exact hres
        rwa [ker_resHom U, Subgroup.mem_subgroupOf] at h1
      have h2 : (k : MulAut W) ∈ K ⊓ centSub U := ⟨k.2, hmem⟩
      rw [hCentBot, Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    · intro hk
      rw [hk]
      exact map_one ρ0
  let ρ : ↥K ≃* ↥(autSub K U) := MulEquiv.ofBijective ρ0 ⟨hinj, hsurj⟩
  have hρ : ∀ (k : ↥K) (w : ↥U),
      U.subtype ((ρ k : MulAut ↥U) w) = (k : MulAut W) (U.subtype w) := by
    intro k w
    show (((ρ k : MulAut ↥U) w : ↥U) : W) = (k : MulAut W) (w : W)
    have happ : (ρ k : MulAut ↥U) = ρ0 k :=
      congrArg (fun x : ↥(autSub K U) => (x : MulAut ↥U))
        (MulEquiv.ofBijective_apply ρ0 ⟨hinj, hsurj⟩ k)
    rw [happ, hρ0apply k, resHom_apply]
  have hirr : ∀ J : Subgroup ↥U,
      (∀ γ ∈ autSub K U, ∀ x ∈ J, γ x ∈ J) → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    have hJdvd : Nat.card ↥J ∣ 2 ^ 2 := by
      have h := Subgroup.card_dvd_of_le (show J ≤ (⊤ : Subgroup ↥U) from le_top)
      simpa [Subgroup.card_top, hU4] using h
    obtain ⟨k, hk2, hkJ⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hJdvd
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl
    · left
      exact Subgroup.card_eq_one.mp (by simpa using hkJ)
    · exfalso
      have hJ2 : Nat.card ↥J = 2 := by simpa using hkJ
      haveI : Nontrivial ↥J := by
        rw [← Finite.one_lt_card_iff_nontrivial, hJ2]
        norm_num
      obtain ⟨j, hj1⟩ := exists_ne (1 : ↥J)
      have hjfix : ((j : ↥U) : W) ∈ fixV K := by
        rw [mem_fixV]
        intro x hx
        have hxstab : x ∈ stabSub U := hKle hx
        have hγ : resHom U ⟨x, hxstab⟩ ∈ autSub K U :=
          mem_autSub.mpr ⟨⟨x, hxstab⟩, hx, rfl⟩
        have hγJ : resHom U ⟨x, hxstab⟩ (j : ↥U) ∈ J := hJ _ hγ (j : ↥U) j.2
        have hγj1 : (⟨resHom U ⟨x, hxstab⟩ (j : ↥U), hγJ⟩ : ↥J) ≠ 1 := by
          intro h
          apply hj1
          have h' : ((⟨resHom U ⟨x, hxstab⟩ (j : ↥U), hγJ⟩ : ↥J) : ↥U) =
              ((1 : ↥J) : ↥U) := congrArg (fun w : ↥J => (w : ↥U)) h
          have h2 : resHom U ⟨x, hxstab⟩ (j : ↥U) = 1 := by simpa using h'
          have h3 : (j : ↥U) = 1 :=
            (resHom U ⟨x, hxstab⟩).injective (by rw [h2, map_one])
          exact Subtype.ext h3
        obtain ⟨z, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥J)).mp hJ2
        have hfixj : (⟨resHom U ⟨x, hxstab⟩ (j : ↥U), hγJ⟩ : ↥J) = j :=
          (huniq _ hγj1).trans (huniq _ hj1).symm
        have h1 : ((resHom U ⟨x, hxstab⟩ (j : ↥U) : ↥U) : W) = ((j : ↥U) : W) :=
          congrArg (fun w : ↥J => ((w : ↥U) : W)) hfixj
        rw [resHom_apply] at h1
        exact h1
      have hmem : ((j : ↥U) : W) ∈ fixV K ⊓ U := ⟨hjfix, (j : ↥U).2⟩
      rw [hfix, Subgroup.mem_bot] at hmem
      have hjU : (j : ↥U) = 1 := Subtype.ext hmem
      exact hj1 (Subtype.ext hjU)
    · right
      refine Subgroup.eq_of_le_of_card_ge le_top ?_
      rw [Subgroup.card_top, hU4, hkJ]
      norm_num
  have hU2 : ∀ x : ↥U, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hW (x : W))
  obtain ⟨π, _, hπ⟩ :=
    CFSG.QuasithinUnique.L246.exists_altDn_three (S := ↥U) hU2 (autSub K U) hΓcard hirr
  have hM : (FFModel.altDn 3).Realizes (autSub K U) ⊤ ⊥ := ⟨π, hπ⟩
  have htrans := s15_Four_realizes_transfer U.subtype U.subtype_injective ρ hρ
    (FFModel.altDn 3) hM
  rw [show (⊤ : Subgroup ↥U).map U.subtype = U from by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype],
      Subgroup.map_bot] at htrans
  exact htrans

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
