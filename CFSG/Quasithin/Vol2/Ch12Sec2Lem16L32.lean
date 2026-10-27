module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16
public import CFSG.Quasithin.Vol2.Ch12Sec4Mod
public import CFSG.Quasithin.H13.L32NoIrrFourProof

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

open Orbit

namespace Lem16L32

variable {V : Type} [CommGroup V]

theorem orbitIn_eq_orbit (H : Subgroup (MulAut V)) (v : V) :
    orbitIn H v = MulAction.orbit ↥H v := by
  ext w
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, h.2, rfl⟩

theorem card_orbitIn_mul [Finite V] (H : Subgroup (MulAut V)) (v : V) :
    Nat.card (orbitIn H v) * Nat.card (MulAction.stabilizer ↥H v) = Nat.card H := by
  rw [orbitIn_eq_orbit, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥H v), mul_comm]
  exact (MulAction.stabilizer ↥H v).card_mul_index

theorem one_lt_card_orbitIn [Finite V] {H : Subgroup (MulAut V)} {v : V} (hv : v ∉ fixV H) :
    ¬ Nat.card (orbitIn H v) ≤ 1 := by
  intro h1
  apply hv
  intro h hh
  have hsub : (orbitIn H v).Subsingleton := by
    rw [← Set.ncard_le_one_iff_subsingleton, ← Nat.card_coe_set_eq]
    exact h1
  exact hsub ⟨h, hh, rfl⟩ ⟨1, H.one_mem, rfl⟩

theorem orbitIn_subset_compl {H : Subgroup (MulAut V)} {v : V} (hv : v ∉ fixV H) :
    orbitIn H v ⊆ ((fixV H : Subgroup V) : Set V)ᶜ := by
  rintro _ ⟨h, hh, rfl⟩ hw
  apply hv
  intro k hk
  have h1 : (h * k * h⁻¹) (h v) = h v :=
    hw (h * k * h⁻¹) (H.mul_mem (H.mul_mem hh hk) (H.inv_mem hh))
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self] at h1
  exact h.injective h1

theorem disjoint_orbitIn {H : Subgroup (MulAut V)} {v w : V} (hw : w ∉ orbitIn H v) :
    Disjoint (orbitIn H v) (orbitIn H w) := by
  rw [Set.disjoint_left]
  rintro _ ⟨g, hg, rfl⟩ ⟨k, hk, hkw⟩
  apply hw
  refine ⟨k⁻¹ * g, H.mul_mem (H.inv_mem hk) hg, ?_⟩
  rw [MulAut.mul_apply, ← hkw, MulAut.inv_apply_self]

theorem not_dvd_factorial_of_le_six {ℓ : ℕ} (h : ℓ ≤ 6) : ¬ 168 ∣ ℓ.factorial := by
  interval_cases ℓ <;> decide

theorem mem_fixV_of_card_orbitIn_le_six [Finite V] {H : Subgroup (MulAut V)}
    (hs : IsSimpleGroup ↥H) (hH : Nat.card H = 168) {v : V}
    (h6 : Nat.card (orbitIn H v) ≤ 6) : v ∈ fixV H := by
  let φ := MulAction.toPermHom ↥H (MulAction.orbit ↥H v)
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hk | hk
  · exfalso
    have hdvd := Subgroup.card_dvd_of_injective φ ((MonoidHom.ker_eq_bot_iff φ).mp hk)
    rw [Nat.card_perm, hH, ← orbitIn_eq_orbit] at hdvd
    exact not_dvd_factorial_of_le_six h6 hdvd
  · intro h hh
    have h1 : φ ⟨h, hh⟩ = 1 := (MonoidHom.mem_ker).mp (hk ▸ Subgroup.mem_top _)
    have h2 := congrArg (fun p : Equiv.Perm (MulAction.orbit ↥H v) =>
      ((p ⟨v, MulAction.mem_orbit_self v⟩ : MulAction.orbit ↥H v) : V)) h1
    simpa [φ] using h2

theorem eight_le_card_orbitIn [Finite V] {H : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥H)
    (hH : Nat.card H = 168)
    (hS : ∀ S : Subgroup (MulAut V), S ≤ H → Nat.card S = 8 → fixV S = fixV H)
    (hV : Nat.card V = 2 ^ 4) (hC : Nat.card (fixV H) = 2) {v : V} (hv : v ∉ fixV H) :
    8 ≤ Nat.card (orbitIn H v) := by
  have hmul := card_orbitIn_mul H v
  rw [hH] at hmul
  have hle : Nat.card (orbitIn H v) ≤ 14 := by
    have h1 : (orbitIn H v).ncard ≤ (((fixV H : Subgroup V) : Set V)ᶜ).ncard :=
      Set.ncard_le_ncard (orbitIn_subset_compl hv) (Set.toFinite _)
    rw [Set.ncard_compl, ← Nat.card_coe_set_eq (((fixV H : Subgroup V) : Set V)),
      ← Nat.card_coe_set_eq] at h1
    have h2 : Nat.card ↥((fixV H : Subgroup V) : Set V) = 2 := hC
    rw [h2, hV] at h1
    omega
  have hge := one_lt_card_orbitIn hv
  have h6 : ¬ Nat.card (orbitIn H v) ≤ 6 := fun h6 =>
    hv (mem_fixV_of_card_orbitIn_le_six hs hH h6)
  by_contra hlt
  have h7 : Nat.card (orbitIn H v) = 7 := by omega
  rw [h7] at hmul
  have hs24 : Nat.card (MulAction.stabilizer ↥H v) = 24 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(MulAction.stabilizer ↥H v)) 2
    (n := 3) (by rw [hs24]; norm_num)
  set S : Subgroup (MulAut V) := (K.map (MulAction.stabilizer ↥H v).subtype).map H.subtype
    with hSdef
  have hSH : S ≤ H := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hS8 : Nat.card S = 8 := by
    rw [hSdef, Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.card_map_of_injective (MulAction.stabilizer ↥H v).subtype_injective, hK]
    norm_num
  have hvS : v ∈ fixV S := by
    rintro _ ⟨_, ⟨k, -, rfl⟩, rfl⟩
    exact (MulAction.mem_stabilizer_iff.mp k.2 :)
  exact hv (hS S hSH hS8 ▸ hvS)

theorem orbitIn_eq_compl [Finite V] {H : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥H)
    (hH : Nat.card H = 168)
    (hS : ∀ S : Subgroup (MulAut V), S ≤ H → Nat.card S = 8 → fixV S = fixV H)
    (hV : Nat.card V = 2 ^ 4) (hC : Nat.card (fixV H) = 2) {v : V} (hv : v ∉ fixV H) :
    orbitIn H v = ((fixV H : Subgroup V) : Set V)ᶜ := by
  refine le_antisymm (orbitIn_subset_compl hv) fun w hw => ?_
  by_contra hwv
  have hwC : w ∉ fixV H := hw
  have hdisj := disjoint_orbitIn hwv
  have h1 : (orbitIn H v ∪ orbitIn H w).ncard ≤ (((fixV H : Subgroup V) : Set V)ᶜ).ncard :=
    Set.ncard_le_ncard (Set.union_subset (orbitIn_subset_compl hv) (orbitIn_subset_compl hwC))
      (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_compl,
    ← Nat.card_coe_set_eq (((fixV H : Subgroup V) : Set V)), ← Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq] at h1
  have h2 : Nat.card ↥((fixV H : Subgroup V) : Set V) = 2 := hC
  rw [h2, hV] at h1
  have h8v := eight_le_card_orbitIn hs hH hS hV hC hv
  have h8w := eight_le_card_orbitIn hs hH hS hV hC hwC
  omega

theorem card_fixV_eq_two [Finite V] (hcard : Nat.card V = 2 ^ 4)
    {X : Subgroup (MulAut V)} (hs : IsSimpleGroup X) (hX : Nat.card X = 168)
    (hcomm : commV X = ⊤) (hC1 : fixV X ≠ ⊥) : Nat.card (fixV X) = 2 := by
  set C := fixV X with hC
  have hK : X ≤ stabSub C := by
    intro g hg u
    constructor
    · intro hu
      have h1 : g⁻¹ (g u) = g u := hu g⁻¹ (X.inv_mem hg)
      have h2 : g⁻¹ (g u) = u := by simp
      rw [h2.symm.trans h1]
      exact hu
    · intro hu
      rw [show g u = u from hu g hg]
      exact hu
  have hdvd : Nat.card C ∣ 2 ^ 4 := hcard ▸ Subgroup.card_subgroup_dvd_card C
  obtain ⟨k, hk, hCk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hC1 (Subgroup.card_eq_one.mp (by rw [hCk]; rfl))
  have hk4 : k ≠ 4 := by
    rintro rfl
    have hCt : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [hCk, hcard])
    have hX1 : X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      refine MulEquiv.ext fun v => ?_
      have hv : v ∈ C := by rw [hCt]; exact Subgroup.mem_top v
      exact hv x hx
    rw [hX1, Subgroup.card_bot] at hX
    omega
  have hsec := card_sec_mul (V := V) (le_top : C ≤ ⊤)
  rw [Subgroup.card_top, hcard, hCk] at hsec
  by_contra hne
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hne (by rw [hCk]; rfl)
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (B5.secHom X (InternalSec.le_stabSub_top X) hK).ker with h | h
  ·
    have : Finite (MulAut (Sec (⊤ : Subgroup V) C)) :=
      Finite.of_injective _ DFunLike.coe_injective
    have hinj := (MonoidHom.ker_eq_bot_iff _).mp h
    have h1 := Subgroup.card_dvd_of_injective _ hinj
    have h2 : Nat.card (MulAut (Sec (⊤ : Subgroup V) C)) ≤
        Nat.card (Equiv.Perm (Sec (⊤ : Subgroup V) C)) :=
      Nat.card_le_card_of_injective (MulAut.toPerm _) fun a b hab =>
        MulEquiv.ext fun x => Equiv.ext_iff.mp hab x
    rw [Nat.card_perm] at h2
    have h3 : Nat.card (Sec (⊤ : Subgroup V) C) ≤ 4 := by
      interval_cases k <;> omega
    have h4 : (Nat.card (Sec (⊤ : Subgroup V) C)).factorial ≤ 24 :=
      (Nat.factorial_le h3).trans (by decide)
    have h5 : 0 < Nat.card (MulAut (Sec (⊤ : Subgroup V) C)) := Nat.card_pos
    rw [hX] at h1
    have := Nat.le_of_dvd h5 h1
    omega
  ·
    have hle : commV X ≤ C := by
      rw [commV, Subgroup.closure_le]
      rintro _ ⟨x, hx, v, rfl⟩
      have hk' : (⟨x, hx⟩ : ↥X) ∈ (B5.secHom X (InternalSec.le_stabSub_top X) hK).ker :=
        h ▸ Subgroup.mem_top _
      exact ((B5.mem_ker_secHom X _ hK _).1 hk').2 v trivial
    rw [hcomm] at hle
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_top, hcard, hCk] at h1
    have : k < 4 := lt_of_le_of_ne hk hk4
    have : 2 ^ k < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) this
    omega

end Lem16L32

open Lem16L32

theorem orbitL32Four_of (hsyl : L32FourSylowFix) : OrbitL32Four := by
  intro V _ _ hV2 hV H hHe hcomm hirr _
  obtain ⟨e⟩ := hHe
  have hH168 : Nat.card H = 168 := (Nat.card_congr e.toEquiv).trans card_sl_three_zmod_two
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two (by norm_num)
  have hs : IsSimpleGroup ↥H := e.isSimpleGroup
  have hC1 : fixV H ≠ ⊥ := by
    intro hC
    obtain ⟨W, hW1, hWt, hWinv⟩ := l32NoIrrFour_holds V hV2 hV H ⟨e⟩
    rcases hirr W (hC ▸ bot_le) hWinv with h | h
    · exact hW1 (h.trans hC)
    · exact hWt h
  have hC2 : Nat.card (fixV H) = 2 := card_fixV_eq_two hV hs hH168 hcomm hC1
  have hnat : BinaryNaturalSL H ⊤ (fixV H) 3 1 :=
    binaryNaturalSL_of_card_sixteen hV2 hV hs hH168 hcomm hC2
  have hS := hsyl V hV2 hV H hcomm hnat
  have hfixone : ∀ x : V, x ∈ fixV H → orbitIn H x = {x} := by
    intro x hx
    ext w
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hx h hh
    · rintro rfl
      exact ⟨1, H.one_mem, rfl⟩
  have hfix_eq : ∀ x y : V, x ∈ fixV H → y ∈ fixV H → x ≠ 1 → y ≠ 1 → x = y := by
    intro x y hx hy hx1 hy1
    by_contra hxy
    have h3 : ({1, x, y} : Set V).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨1, x, y, hx1.symm, hy1.symm, hxy, rfl⟩
    have h4 : ({1, x, y} : Set V).ncard ≤ ((fixV H : Subgroup V) : Set V).ncard := by
      refine Set.ncard_le_ncard ?_ (Set.toFinite _)
      rintro _ (rfl | rfl | rfl)
      · exact (fixV H).one_mem
      · exact hx
      · exact hy
    have h5 : ((fixV H : Subgroup V) : Set V).ncard = 2 := by
      rw [← Nat.card_coe_set_eq]
      exact hC2
    omega
  have hcompl : (((fixV H : Subgroup V) : Set V)ᶜ).ncard = 14 := by
    rw [Set.ncard_compl, ← Nat.card_coe_set_eq (((fixV H : Subgroup V) : Set V))]
    have h5 : Nat.card ↥((fixV H : Subgroup V) : Set V) = 2 := hC2
    rw [h5, hV]
    norm_num
  have hlen : ∀ x : V, x ∉ fixV H → Nat.card (orbitIn H x) = 14 := by
    intro x hx
    rw [orbitIn_eq_compl hs hH168 hS hV hC2 hx, Nat.card_coe_set_eq, hcompl]
  refine ⟨fun v hv1 => ?_, fun v w hv1 hw1 hvw => ?_⟩
  · by_cases hv : v ∈ fixV H
    · rw [hfixone v hv, Nat.card_coe_set_eq, Set.ncard_singleton]
      simp
    · rw [hlen v hv]
      simp
  · by_cases hv : v ∈ fixV H <;> by_cases hw : w ∈ fixV H
    · exact ⟨1, H.one_mem, by rw [hfix_eq v w hv hw hv1 hw1]; rfl⟩
    · rw [hfixone v hv, Nat.card_coe_set_eq, Set.ncard_singleton, hlen w hw] at hvw
      omega
    · rw [hlen v hv, hfixone w hw, Nat.card_coe_set_eq, Set.ncard_singleton] at hvw
      omega
    · have hwo : w ∈ orbitIn H v := by
        rw [orbitIn_eq_compl hs hH168 hS hV hC2 hv]
        exact hw
      exact hwo

theorem stmt12_2_16_of_sylowFix (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1) (hL52 : OrbitL52Ten)
    (hsyl : L32FourSylowFix) (hHat : OrbitHatA6Six) (hG2c : G2NaturalCover)
    (h6 : CoreSixTwoCentral) (hW : G2WeylTwoCentral) (h8 : Lem12216CoreEight) :
    Stmt12_2_16 :=
  stmt12_2_16_of h1222 h331 hL52 (orbitL32Four_of hsyl) hHat hG2c h6 hW h8

end CFSG.Quasithin.H13
