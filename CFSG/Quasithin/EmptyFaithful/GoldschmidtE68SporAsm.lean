module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporCrit
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporSylow
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporSound
public import CFSG.Quasithin.H13.GoldschmidtC137H6Alg

public section

namespace CFSG.Quasithin.E6.Spor

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.S151S9T.LatAux CFSG.Quasithin.E2P.SporB

theorem cent2NoComp_of_solvable {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ}
    (hS : IsSylowTwoOf S ⊤) {z₀ : Γ} (hz2 : orderOf z₀ = 2)
    (hZ : S ⊓ centralizer (S : Set Γ) = Subgroup.zpowers z₀) {k N : ℕ} (hN : Odd N)
    (hΓ : Nat.card Γ = 2 ^ k * N) (hSk : Nat.card S = 2 ^ k)
    (hle : Nat.card (centralizer ({z₀} : Set Γ)) ≤ 3 * 2 ^ k) : Cent2NoComp Γ := by
  refine cent2NoComp_of_centre hS hz2 hZ ?_
  intro B
  have hz : z₀ ∈ S ⊓ centralizer (S : Set Γ) := by
    rw [hZ]
    exact Subgroup.mem_zpowers z₀
  have hSle : S ≤ centralizer ({z₀} : Set Γ) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hz.2 s hs)
  have hdvd1 : Nat.card (centralizer ({z₀} : Set Γ)) ∣ 2 ^ k * N := by
    rw [← hΓ]
    exact Subgroup.card_subgroup_dvd_card _
  have hdvd2 : 2 ^ k ∣ Nat.card (centralizer ({z₀} : Set Γ)) := by
    rw [← hSk]
    exact Subgroup.card_dvd_of_le hSle
  exact noComponent_of_card_le hN hdvd1 hdvd2 hle B

theorem cent2NoComp_of_rData {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ}
    (hS : IsSylowTwoOf S ⊤) {z₀ : Γ} (hz2 : orderOf z₀ = 2)
    (hZ : S ⊓ centralizer (S : Set Γ) = Subgroup.zpowers z₀) {k r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hcard : Nat.card (centralizer ({z₀} : Set Γ)) = 2 ^ k * 3 * r)
    {y x : Γ} (hy : y * z₀ = z₀ * y) (hyr : orderOf y = r)
    (hx : x ∈ pCoreOf 2 (centralizer ({z₀} : Set Γ))) (hyx : y * x ≠ x * y) : Cent2NoComp Γ := by
  refine cent2NoComp_of_centre hS hz2 hZ ?_
  intro B
  have hyC : y ∈ centralizer ({z₀} : Set Γ) := Subgroup.mem_centralizer_singleton_iff.mpr hy
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
  refine noComponent_of_rElement (C := ↥(centralizer ({z₀} : Set Γ))) hr hr2 hr3 hcard
    (y := ⟨y, hyC⟩) (n := x') ?_ hx' ?_ B
  · exact (Subgroup.orderOf_coe ⟨y, hyC⟩).symm.trans hyr
  · intro h
    exact hyx (congrArg Subtype.val h)

section Class

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem card_le_of_classChk {a b z₀ : Γ} (hgen : Subgroup.closure ({a, b} : Set Γ) = ⊤)
    {zT ta tb : Array ℕ} (hzT : (tab n z₀).toArray = zT) (ha : (tab n a).toArray = ta)
    (hb : (tab n b).toArray = tb) {s : ℕ} (hcl : classChk n ta tb zT s = true) :
    0 < s ∧ Nat.card (centralizer ({z₀} : Set Γ)) * s ≤ Nat.card Γ := by
  obtain ⟨-, O, hO, hOs⟩ := classChk_sound hcl
  subst ha hb
  have hle := card_centralizer_mul_le hgen hzT hO
  rw [hOs] at hle
  exact ⟨hOs ▸ hO.2.1, hle⟩

theorem cent2NoComp_of_class_only {a b : Γ} (hgen : Subgroup.closure ({a, b} : Set Γ) = ⊤)
    {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) {z₀ : Γ} (hz2 : orderOf z₀ = 2)
    (hZ : S ⊓ centralizer (S : Set Γ) = Subgroup.zpowers z₀) {zT ta tb : Array ℕ}
    (hzT : (tab n z₀).toArray = zT) (ha : (tab n a).toArray = ta) (hb : (tab n b).toArray = tb)
    {s k N : ℕ} (hcl : classChk n ta tb zT s = true) (hN : Odd N) (hΓ : Nat.card Γ = 2 ^ k * N)
    (hSk : Nat.card S = 2 ^ k) (hnum : Nat.card Γ = s * (3 * 2 ^ k)) : Cent2NoComp Γ := by
  obtain ⟨hs, hle⟩ := card_le_of_classChk hgen hzT ha hb hcl
  refine cent2NoComp_of_solvable hS hz2 hZ hN hΓ hSk ?_
  rw [hnum, mul_comm s] at hle
  exact Nat.le_of_mul_le_mul_right hle hs

end Class

section RRoute

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

omit [FaithfulSMul Γ (Fin n)] in
theorem genOver_le_centralizer (C : LatCtx Γ n Lab) {z₀ : Γ}
    (hZ : C.S ⊓ centralizer (C.S : Set Γ) = Subgroup.zpowers z₀) {us : List Γ}
    (hu : ∀ u ∈ us, u * z₀ = z₀ * u) : genOver C us ≤ centralizer ({z₀} : Set Γ) := by
  have hz : z₀ ∈ C.S ⊓ centralizer (C.S : Set Γ) := by
    rw [hZ]
    exact Subgroup.mem_zpowers z₀
  unfold genOver
  rw [Subgroup.closure_le]
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz.2 g (C.sg_mem_S g hg))
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hu g hg)

omit [FaithfulSMul Γ (Fin n)] in
theorem cent2NoComp_of_class_route (C : LatCtx Γ n Lab) (hS : IsSylowTwoOf C.S ⊤) {z₀ : Γ}
    (hz2 : orderOf z₀ = 2) (hZ : C.S ⊓ centralizer (C.S : Set Γ) = Subgroup.zpowers z₀)
    {zT : Array ℕ} (hzT : (tab n z₀).toArray = zT) {s m r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hcl : classChk n C.ta C.tb zT s = true) (hR : RWit C z₀ r m)
    (hm : m = 3 * r) (hodd : m % 2 = 1) (hnum : s * (m * 2 ^ C.k) = Nat.card Γ) :
    Cent2NoComp Γ := by
  obtain ⟨hs, hle⟩ := card_le_of_classChk C.gen hzT C.ha C.hb hcl
  obtain ⟨us, uTabs, OH, y, x, hus, hucomm, hOH, hOHm, hy, hyr, hxS, hxfix, hyx⟩ := hR
  have hHcard := card_gen hus hOH
  rw [hOHm] at hHcard
  have hHle := genOver_le_centralizer C hZ hucomm
  have hCeq : centralizer ({z₀} : Set Γ) = genOver C us := by
    refine (Subgroup.eq_of_le_of_card_ge hHle ?_).symm
    rw [hHcard]
    rw [← hnum] at hle
    exact Nat.le_of_mul_le_mul_right (by linarith) hs
  have hcard : Nat.card (centralizer ({z₀} : Set Γ)) = 2 ^ C.k * 3 * r := by
    rw [hCeq, hHcard, hm]
    ring
  have hx : x ∈ pCoreOf 2 (centralizer ({z₀} : Set Γ)) := by
    rw [hCeq]
    exact mem_pCoreOf_gen hus hOH (by rw [hOHm]; exact hodd) hxS hxfix
  exact cent2NoComp_of_rData hS hz2 hZ hr hr2 hr3 hcard hy hyr hx hyx

omit [FaithfulSMul Γ (Fin n)] in
theorem cent2NoComp_of_lat_route (C : LatCtx Γ n Lab) {Ls : Array ℕ}
    (hL : C.D.Om.map (fun o => o.lbl.size) = Ls) (hS : IsSylowTwoOf C.S ⊤) {z₀ : Γ}
    (hz2 : orderOf z₀ = 2) (hZ : C.S ⊓ centralizer (C.S : Set Γ) = Subgroup.zpowers z₀)
    (hnc : ¬ ∀ g : Γ, g * z₀ = z₀ * g) {q : ℕ}
    (huniq : ∀ j < Ls.size, Ls[j]! = Ls[q]! → j = q)
    (hmax : ∀ j < Ls.size, C.Y q ≤ C.Y j → j = q) {m r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hR : RWit C z₀ r m) (hmq : m = Ls[q]!) (hm : m = 3 * r)
    (hodd : m % 2 = 1) : Cent2NoComp Γ := by
  obtain ⟨us, uTabs, OH, y, x, hus, hucomm, hOH, hOHm, hy, hyr, hxS, hxfix, hyx⟩ := hR
  have hHcard := card_gen hus hOH
  rw [hOHm] at hHcard
  have hHle := genOver_le_centralizer C hZ hucomm
  have hne : centralizer ({z₀} : Set Γ) ≠ ⊤ := fun h => hnc fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (h ▸ Subgroup.mem_top g)
  have hSH := S_le_genOver C us
  have hHq : genOver C us = C.Y q := by
    rcases lat_cases C hL hSH with ⟨j, hj, hjeq⟩ | htop
    · have h1 := lat_card C hL j hj
      rw [← hjeq, hHcard, hmq] at h1
      have h2 : Ls[j]! = Ls[q]! :=
        (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h1).symm
      rw [hjeq, huniq j hj h2]
    · exfalso
      exact hne (top_le_iff.mp (htop ▸ hHle))
  have hCeq : centralizer ({z₀} : Set Γ) = genOver C us := by
    rcases lat_cases C hL (hSH.trans hHle) with ⟨j, hj, hjeq⟩ | htop
    · have : C.Y q ≤ C.Y j := by rw [← hHq, ← hjeq]; exact hHle
      rw [hjeq, hHq, hmax j hj this]
    · exact absurd htop hne
  have hcard : Nat.card (centralizer ({z₀} : Set Γ)) = 2 ^ C.k * 3 * r := by
    rw [hCeq, hHcard, hm]
    ring
  have hx : x ∈ pCoreOf 2 (centralizer ({z₀} : Set Γ)) := by
    rw [hCeq]
    exact mem_pCoreOf_gen hus hOH (by rw [hOHm]; exact hodd) hxS hxfix
  exact cent2NoComp_of_rData hS hz2 hZ hr hr2 hr3 hcard hy hyr hx hyx

end RRoute

end CFSG.Quasithin.E6.Spor
