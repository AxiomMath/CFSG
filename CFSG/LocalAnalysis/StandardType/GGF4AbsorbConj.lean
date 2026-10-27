module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGF4ReflLin
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

omit [Finite G] in
private lemma f4Conj_apply_conj_eq_inv {tK tX w : MulAut ↥Bs} {y : ↥Bs}
    (hw : w * tK * w⁻¹ = tX) (hy : tK y = y⁻¹) : tX (w y) = (w y)⁻¹ := by
  calc tX (w y) = (w * tK * w⁻¹) (w y) := by rw [hw]
    _ = w (tK (w⁻¹ (w y))) := rfl
    _ = w (tK y) := by rw [MulAut.inv_apply_self]
    _ = w y⁻¹ := by rw [hy]
    _ = (w y)⁻¹ := map_inv w y

private lemma f4Conj_zpowers_eq_of_inverts (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    {t : MulAut ↥Bs} (ht : GGIsReflection p t) {u v : ↥Bs} (hu : u ≠ 1) (hv : v ≠ 1)
    (htu : t u = u⁻¹) (htv : t v = v⁻¹) : Subgroup.zpowers u = Subgroup.zpowers v := by
  have huv : v ∈ Subgroup.zpowers u :=
    GGIsReflection.mem_zpowers_of_apply_eq_inv hp2 hBs ht hu htu htv
  have hvu : u ∈ Subgroup.zpowers v :=
    GGIsReflection.mem_zpowers_of_apply_eq_inv hp2 hBs ht hv htv htu
  exact le_antisymm (Subgroup.zpowers_le.mpr hvu) (Subgroup.zpowers_le.mpr huv)

private lemma f4Conj_exists_lift_and_zpowers (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    {H X K : Subgroup G} {u y : G} (hX : GGFixLineComp Bs u X) (hK : GGFixLineComp Bs y K)
    (hu1 : u ≠ 1) (hy1 : y ≠ 1) {A : Subgroup (MulAut ↥Bs)}
    (hAH : A ≤ ggAutomizer H Bs) {tX tK w : MulAut ↥Bs} (hwA : w ∈ A)
    (hw : w * tK * w⁻¹ = tX) (htX : GGIsReflection p tX)
    (htXu : tX ⟨u, hX.mem⟩ = ⟨u, hX.mem⟩⁻¹)
    (htKy : tK ⟨y, hK.mem⟩ = ⟨y, hK.mem⟩⁻¹) :
    ∃ (h : G) (_ : h ∈ H) (_ : h ∈ Subgroup.normalizer (Bs : Set G)),
      (∀ b : ↥Bs, ((w b : ↥Bs) : G) = h * b * h⁻¹) ∧
        Subgroup.zpowers u = Subgroup.zpowers (h * y * h⁻¹) := by
  obtain ⟨h, hhH, hhN, hwh⟩ := mem_ggAutomizer_iff.mp (hAH hwA)
  refine ⟨h, hhH, hhN, hwh, ?_⟩
  set v : ↥Bs := w ⟨y, hK.mem⟩ with hvdef
  have hvG : (v : G) = h * y * h⁻¹ := by
    rw [hvdef]
    exact hwh ⟨y, hK.mem⟩
  have htv : tX v = v⁻¹ := by
    rw [hvdef]
    exact f4Conj_apply_conj_eq_inv hw htKy
  have hu1' : (⟨u, hX.mem⟩ : ↥Bs) ≠ 1 :=
    fun h1 => hu1 (by simpa using congrArg Subtype.val h1)
  have hv1 : v ≠ 1 := by
    rw [hvdef]
    intro h1
    have h2 : (⟨y, hK.mem⟩ : ↥Bs) = 1 := w.injective (by rw [h1, map_one])
    exact hy1 (by simpa using congrArg Subtype.val h2)
  have hzv : Subgroup.zpowers (⟨u, hX.mem⟩ : ↥Bs) = Subgroup.zpowers v :=
    f4Conj_zpowers_eq_of_inverts hp2 hBs htX hu1' hv1 htXu htv
  have hsub : (Bs.subtype v : G) = h * y * h⁻¹ := hvG
  have h1 : (Subgroup.zpowers (⟨u, hX.mem⟩ : ↥Bs)).map Bs.subtype =
      (Subgroup.zpowers v).map Bs.subtype := by rw [hzv]
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, hsub] at h1
  exact h1

omit [Finite G] in
private lemma f4Conj_automizer_map_conj_eq {K : Subgroup G} {h : G}
    (hhN : h ∈ Subgroup.normalizer (Bs : Set G)) {w : MulAut ↥Bs}
    (hwh : ∀ b : ↥Bs, ((w b : ↥Bs) : G) = h * b * h⁻¹) :
    ggAutomizer (K.map (MulAut.conj h).toMonoidHom) Bs =
      (ggAutomizer K Bs).map (MulAut.conj w).toMonoidHom := by
  have hw_eq : ggConjAut Bs hhN = w := by
    ext b
    rw [ggConjAut_apply]
    exact (hwh b).symm
  rw [ggAutomizer_map_conj hhN K, hw_eq]

omit [Finite G] in
private lemma f4Conj_map_conj_le_centralizer {A P : Subgroup (MulAut ↥Bs)}
    {tX tK w : MulAut ↥Bs} (hwA : w ∈ A) (hw : w * tK * w⁻¹ = tX) (hPA : P ≤ A)
    (hPc : ∀ φ ∈ P, φ * tK = tK * φ) :
    P.map (MulAut.conj w).toMonoidHom ≤
      A ⊓ Subgroup.centralizer ({tX} : Set (MulAut ↥Bs)) := by
  refine le_inf ?_ ?_
  · rintro φ ⟨ψ, hψ, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact A.mul_mem (A.mul_mem hwA (hPA hψ)) (A.inv_mem hwA)
  · rintro φ ⟨ψ, hψ, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hw]
    have hcomm : ψ * tK = tK * ψ := hPc ψ hψ
    calc w * ψ * w⁻¹ * (w * tK * w⁻¹) = w * (ψ * tK) * w⁻¹ := by group
      _ = w * (tK * ψ) * w⁻¹ := by rw [hcomm]
      _ = w * tK * w⁻¹ * (w * ψ * w⁻¹) := by group

omit [Finite G] in
private lemma f4Conj_six_le_card_inf [Finite (MulAut ↥Bs)] {P Q C : Subgroup (MulAut ↥Bs)}
    (hPC : P ≤ C) (hQC : Q ≤ C)
    (hP : Nat.card ↥P = 24 ∨ Nat.card ↥P = 48)
    (hQ : Nat.card ↥Q = 24 ∨ Nat.card ↥Q = 48)
    (hC : Nat.card ↥C ≤ 96) :
    6 ≤ Nat.card ↥(P ⊓ Q) := by
  have h1 : P.relIndex C * Nat.card ↥P = Nat.card ↥C := by
    have h := Subgroup.relIndex_mul_card (H := P) (K := C)
    rwa [inf_of_le_left hPC] at h
  have h2 : Q.relIndex C * Nat.card ↥Q = Nat.card ↥C := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := C)
    rwa [inf_of_le_left hQC] at h
  have h3 : (P ⊓ Q).relIndex C * Nat.card ↥(P ⊓ Q) = Nat.card ↥C := by
    have h := Subgroup.relIndex_mul_card (H := P ⊓ Q) (K := C)
    rwa [inf_of_le_left (le_trans inf_le_left hPC)] at h
  have hle : (P ⊓ Q).relIndex C ≤ P.relIndex C * Q.relIndex C :=
    Subgroup.relIndex_inf_le
  have h4 : (P ⊓ Q).relIndex C * Nat.card ↥P * Nat.card ↥Q ≤
      Nat.card ↥C * Nat.card ↥C := by
    calc (P ⊓ Q).relIndex C * Nat.card ↥P * Nat.card ↥Q
        ≤ (P.relIndex C * Q.relIndex C) * Nat.card ↥P * Nat.card ↥Q :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
      _ = (P.relIndex C * Nat.card ↥P) * (Q.relIndex C * Nat.card ↥Q) := by ring
      _ = Nat.card ↥C * Nat.card ↥C := by rw [h1, h2]
  have h5 : Nat.card ↥P * Nat.card ↥Q ≤ Nat.card ↥(P ⊓ Q) * Nat.card ↥C := by
    have hcpos : 0 < Nat.card ↥C := Nat.card_pos_iff.2 ⟨⟨(1 : ↥C)⟩, inferInstance⟩
    refine Nat.le_of_mul_le_mul_left ?_ hcpos
    calc Nat.card ↥C * (Nat.card ↥P * Nat.card ↥Q)
        = (P ⊓ Q).relIndex C * Nat.card ↥(P ⊓ Q) * Nat.card ↥P * Nat.card ↥Q := by
          rw [h3]; ring
      _ = Nat.card ↥(P ⊓ Q) * ((P ⊓ Q).relIndex C * Nat.card ↥P * Nat.card ↥Q) := by ring
      _ ≤ Nat.card ↥(P ⊓ Q) * (Nat.card ↥C * Nat.card ↥C) := Nat.mul_le_mul_left _ h4
      _ = Nat.card ↥C * (Nat.card ↥(P ⊓ Q) * Nat.card ↥C) := by ring
  have hp : 24 ≤ Nat.card ↥P := by rcases hP with h | h <;> omega
  have hq : 24 ≤ Nat.card ↥Q := by rcases hQ with h | h <;> omega
  have hnc : 576 ≤ Nat.card ↥(P ⊓ Q) * Nat.card ↥C := by
    calc 576 = 24 * 24 := by norm_num
      _ ≤ Nat.card ↥P * Nat.card ↥Q := Nat.mul_le_mul hp hq
      _ ≤ Nat.card ↥(P ⊓ Q) * Nat.card ↥C := h5
  have h96 : Nat.card ↥(P ⊓ Q) * Nat.card ↥C ≤ Nat.card ↥(P ⊓ Q) * 96 :=
    Nat.mul_le_mul_left _ hC
  omega

private lemma f4Conj_two_dvd_of_six_le_dvd {n : ℕ} (h6 : 6 ≤ n) (hdvd : n ∣ 24 ∨ n ∣ 48) :
    2 ∣ n := by
  rcases hdvd with h | h
  · have hle : n ≤ 24 := Nat.le_of_dvd (by norm_num) h
    interval_cases n <;> norm_num at h
    all_goals norm_num
  · have hle : n ≤ 48 := Nat.le_of_dvd (by norm_num) h
    interval_cases n <;> norm_num at h
    all_goals norm_num

omit [Finite G] in
private lemma f4Conj_eq_one_of_mul_self_eq_one (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    {b : G} (hb : b ∈ Bs) (hb2 : b * b = 1) : b = 1 := by
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have h1 : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hb2)
  have h2 : orderOf b ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hBs.2 b hb)
  have h3 : orderOf b ∣ 1 := by
    have h := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

omit [Finite G] in
private lemma f4Conj_fix_iff_of_zpowers_eq {X K' : Subgroup G} {u v : G}
    (hX : GGFixLineComp Bs u X) (hK' : GGFixLineComp Bs v K')
    (hzp : Subgroup.zpowers u = Subgroup.zpowers v) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) ↔ ∀ φ ∈ ggAutomizer K' Bs, φ b = b := by
  intro b
  have h1 := hX.fix_iff b
  have h2 := hK'.fix_iff b
  rw [hzp] at h1
  exact h1.trans h2.symm

private lemma f4Conj_eq_of_fix_iff [Finite (MulAut ↥Bs)]
    (hBs2 : ∀ b ∈ Bs, b * b = 1 → b = 1)
    {X K' : Subgroup G} {u v : G} (hX : GGFixLineComp Bs u X) (hK' : GGFixLineComp Bs v K')
    (hBX : Bs ≤ Subgroup.normalizer (X : Set G))
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) ↔
      ∀ φ ∈ ggAutomizer K' Bs, φ b = b)
    {C : Subgroup (MulAut ↥Bs)} (hXsub : ggAutomizer X Bs ≤ C)
    (hKsub : ggAutomizer K' Bs ≤ C)
    (hXcard : Nat.card ↥(ggAutomizer X Bs) = 24 ∨ Nat.card ↥(ggAutomizer X Bs) = 48)
    (hKcard : Nat.card ↥(ggAutomizer K' Bs) = 24 ∨ Nat.card ↥(ggAutomizer K' Bs) = 48)
    (hC : Nat.card ↥C ≤ 96) : X = K' := by
  have : Finite ↥(ggAutomizer X Bs ⊓ ggAutomizer K' Bs) := Subtype.finite
  have hn6 : 6 ≤ Nat.card ↥(ggAutomizer X Bs ⊓ ggAutomizer K' Bs) :=
    f4Conj_six_le_card_inf (P := ggAutomizer X Bs) (Q := ggAutomizer K' Bs) (C := C)
      hXsub hKsub hXcard hKcard hC
  have h2n : 2 ∣ Nat.card ↥(ggAutomizer X Bs ⊓ ggAutomizer K' Bs) := by
    refine f4Conj_two_dvd_of_six_le_dvd hn6 ?_
    have hdvd : Nat.card ↥(ggAutomizer X Bs ⊓ ggAutomizer K' Bs) ∣
        Nat.card ↥(ggAutomizer X Bs) := Subgroup.card_dvd_of_le inf_le_left
    rcases hXcard with h | h
    · left; rwa [h] at hdvd
    · right; rwa [h] at hdvd
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(ggAutomizer X Bs ⊓ ggAutomizer K' Bs)) 2 h2n
  have hrP : (r : MulAut ↥Bs) ∈ ggAutomizer X Bs := r.2.1
  have hrQ : (r : MulAut ↥Bs) ∈ ggAutomizer K' Bs := r.2.2
  have hr2 : (r : MulAut ↥Bs) ^ 2 = 1 := by
    have h1 : r ^ 2 = 1 := by rw [← hr]; exact pow_orderOf_eq_one r
    simpa using congrArg (fun x : ↥(ggAutomizer X Bs ⊓ ggAutomizer K' Bs) => (x : MulAut ↥Bs)) h1
  have hr1 : (r : MulAut ↥Bs) ≠ 1 := by
    intro h1
    have h2 : r = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hr
    omega
  exact GGFixLineComp.eq_of_fix_iff hX hK' hBs2 hBX hfix hrP hrQ hr2 hr1

omit [Finite G] in
private lemma f4Conj_le_of_map_conj_eq {H X K K' : Subgroup G} {h : G}
    (hK'def : K' = K.map (MulAut.conj h).toMonoidHom) (hXK' : X = K')
    (hhH : h ∈ H) (hXH : X ≤ H) : K ≤ H := by
  have hKle : K ≤ K'.map (MulAut.conj h⁻¹).toMonoidHom := by
    intro k hk
    rw [hK'def]
    refine Subgroup.mem_map.mpr ⟨MulAut.conj h k, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hmap : K'.map (MulAut.conj h⁻¹).toMonoidHom ≤ H ⊔ X := by
    rw [hXK']
    exact map_conj_le_sup (Subgroup.inv_mem H hhH)
  have hKH : K ≤ H ⊔ X := hKle.trans hmap
  rwa [sup_eq_left.mpr hXH] at hKH

theorem GGFixLineComp.exists_eq_map_conj_of_conj_endpointRefl (hp2 : p ≠ 2)
    (hBs : IsElemAbelian p Bs)
    {H X K : Subgroup G} {u y : G} (hX : GGFixLineComp Bs u X) (hK : GGFixLineComp Bs y K)
    (hBX : Bs ≤ Subgroup.normalizer (X : Set G)) (hu1 : u ≠ 1) (hy1 : y ≠ 1)
    {A : Subgroup (MulAut ↥Bs)} (hAH : A ≤ ggAutomizer H Bs) {tX tK w : MulAut ↥Bs}
    (hwA : w ∈ A) (hw : w * tK * w⁻¹ = tX) (htX : GGIsReflection p tX)
    (htXu : tX ⟨u, hX.mem⟩ = ⟨u, hX.mem⟩⁻¹) (htKy : tK ⟨y, hK.mem⟩ = ⟨y, hK.mem⟩⁻¹)
    (hXA : ggAutomizer X Bs ≤ A) (hKA : ggAutomizer K Bs ≤ A)
    (hXc : ∀ φ ∈ ggAutomizer X Bs, φ * tX = tX * φ)
    (hKc : ∀ φ ∈ ggAutomizer K Bs, φ * tK = tK * φ)
    (hXcard : Nat.card ↥(ggAutomizer X Bs) = 24 ∨ Nat.card ↥(ggAutomizer X Bs) = 48)
    (hKcard : Nat.card ↥(ggAutomizer K Bs) = 24 ∨ Nat.card ↥(ggAutomizer K Bs) = 48)
    (hC : Nat.card ↥(A ⊓ Subgroup.centralizer ({tX} : Set (MulAut ↥Bs))) ≤ 96) :
    ∃ h ∈ H, h ∈ Subgroup.normalizer (Bs : Set G) ∧ X = K.map (MulAut.conj h).toMonoidHom := by
  have : Finite ↥Bs := Subtype.finite
  have : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun f : MulAut ↥Bs => (f : ↥Bs → ↥Bs)) DFunLike.coe_injective
  obtain ⟨h, hhH, hhN, hwh, hzp⟩ :=
    f4Conj_exists_lift_and_zpowers hp2 hBs hX hK hu1 hy1 hAH hwA hw htX htXu htKy
  obtain ⟨K', hK', hK'def⟩ : ∃ K' : Subgroup G, GGFixLineComp Bs (h * y * h⁻¹) K' ∧
      K' = K.map (MulAut.conj h).toMonoidHom := ⟨_, hK.map_conj hhN, rfl⟩
  have hQeq : ggAutomizer K' Bs = (ggAutomizer K Bs).map (MulAut.conj w).toMonoidHom := by
    rw [hK'def]
    exact f4Conj_automizer_map_conj_eq hhN hwh
  have hCmem : ggAutomizer K' Bs ≤
      A ⊓ Subgroup.centralizer ({tX} : Set (MulAut ↥Bs)) := by
    rw [hQeq]
    exact f4Conj_map_conj_le_centralizer (P := ggAutomizer K Bs) hwA hw hKA hKc
  have hXmem : ggAutomizer X Bs ≤
      A ⊓ Subgroup.centralizer ({tX} : Set (MulAut ↥Bs)) :=
    le_inf hXA fun φ hφ => Subgroup.mem_centralizer_singleton_iff.mpr (hXc φ hφ)
  have hQcard : Nat.card ↥(ggAutomizer K' Bs) = 24 ∨
      Nat.card ↥(ggAutomizer K' Bs) = 48 := by
    rw [hQeq, Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact hKcard
  have hXK' : X = K' :=
    f4Conj_eq_of_fix_iff (X := X) (K' := K')
      (C := A ⊓ Subgroup.centralizer ({tX} : Set (MulAut ↥Bs)))
      (fun b hb hb2 => f4Conj_eq_one_of_mul_self_eq_one hp2 hBs hb hb2)
      hX hK' hBX (f4Conj_fix_iff_of_zpowers_eq hX hK' hzp) hXmem hCmem hXcard hQcard hC
  exact ⟨h, hhH, hhN, hXK'.trans hK'def⟩

theorem GGFixLineComp.le_of_conj_endpointRefl (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    {H X K : Subgroup G} {u y : G} (hX : GGFixLineComp Bs u X) (hK : GGFixLineComp Bs y K)
    (hXH : X ≤ H) (hBX : Bs ≤ Subgroup.normalizer (X : Set G)) (hu1 : u ≠ 1) (hy1 : y ≠ 1)
    {A : Subgroup (MulAut ↥Bs)} (hAH : A ≤ ggAutomizer H Bs) {tX tK w : MulAut ↥Bs}
    (hwA : w ∈ A) (hw : w * tK * w⁻¹ = tX) (htX : GGIsReflection p tX)
    (htXu : tX ⟨u, hX.mem⟩ = ⟨u, hX.mem⟩⁻¹) (htKy : tK ⟨y, hK.mem⟩ = ⟨y, hK.mem⟩⁻¹)
    (hXA : ggAutomizer X Bs ≤ A) (hKA : ggAutomizer K Bs ≤ A)
    (hXc : ∀ φ ∈ ggAutomizer X Bs, φ * tX = tX * φ)
    (hKc : ∀ φ ∈ ggAutomizer K Bs, φ * tK = tK * φ)
    (hXcard : Nat.card ↥(ggAutomizer X Bs) = 24 ∨ Nat.card ↥(ggAutomizer X Bs) = 48)
    (hKcard : Nat.card ↥(ggAutomizer K Bs) = 24 ∨ Nat.card ↥(ggAutomizer K Bs) = 48)
    (hC : Nat.card ↥(A ⊓ Subgroup.centralizer ({tX} : Set (MulAut ↥Bs))) ≤ 96) :
    K ≤ H := by
  obtain ⟨h, hhH, -, hXK⟩ := GGFixLineComp.exists_eq_map_conj_of_conj_endpointRefl hp2 hBs hX hK
    hBX hu1 hy1 hAH hwA hw htX htXu htKy hXA hKA hXc hKc hXcard hKcard hC
  exact f4Conj_le_of_map_conj_eq rfl hXK hhH hXH

end CFSG.StandardType

end
