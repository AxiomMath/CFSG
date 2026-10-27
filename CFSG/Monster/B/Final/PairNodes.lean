module

public import CFSG.Monster.B.Final.Simple
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3049
public import Certificates.Certificate3109
public import Certificates.Certificate3027
public import CFSG.Monster.B.TwoA.Co2Inv.KerElts
public import CFSG.Monster.B.TwoA.Co2Inv.SixAction

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open Matrix MulOpposite Bin CFSG.Blueprint CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Visible CFSG.Monster.B.Rep4371

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] noncomputable def qA : Q := pauliQ (false, 1078, 64)

theorem qA_eq : qA = qElt 1 * qElt 2 * qElt 4 * qElt 5 * qElt 10 * qElt 17 := by
  simp only [qElt_eq, ← pauliQ_mul]
  rw [qA]
  congr 1

theorem qA_mul_rStar : qA * Short.rStar = Short.rStar * qA := by
  have h : Model.Pauli.mul (false, 1078, 64) (false, 0, 191) =
      Model.Pauli.mul (false, 0, 191) (false, 1078, 64) := by decide
  rw [qA, rStar_eq, ← pauliQ_mul, ← pauliQ_mul, h]

theorem qA_mem : qA ∈ Subgroup.centralizer {Short.rStar} :=
  Subgroup.mem_centralizer_singleton_iff.2 qA_mul_rStar

@[expose] noncomputable def a0 : Cbar :=
  kappa ⟨rhoEquiv qA * hElt 5, Cgen.mul_mem (rhoEquiv_mem_Cgen qA_mem) (hElt_mem_Cgen 5)⟩

@[expose] noncomputable def WB : Sbp := wordS gSeq conjWord0

@[expose] noncomputable def aB : Sbp := WB⁻¹ * op a0 * WB

@[expose] noncomputable def bB : Sbp := op taubar

@[expose] noncomputable def HB : Subgroup Sbp := Subgroup.closure {aB, bB}

theorem gSeq_six : gSeq 6 = kappa ⟨hElt 5, hElt_mem_Cgen 5⟩ := by
  rw [gSeq_of_lt (by norm_num)]
  exact selGen_succ 5

theorem gSeq_zero : gSeq 0 = kappa ⟨rhoEquiv (qElt 1), rhoEquiv_qElt_mem_Cgen 1⟩ := by
  rw [gSeq_of_lt (by norm_num)]
  exact selGen_zero

theorem gSeq_succ (i : Fin 24) : gSeq (i + 1) = kappa ⟨hElt i, hElt_mem_Cgen i⟩ := by
  rw [gSeq_of_lt (by omega)]
  exact selGen_succ i

theorem packetElt_kappa_qElt (k : Fin 23) :
    packetElt ⟨k, by omega⟩ = kappa ⟨rhoEquiv (qElt k), rhoEquiv_qElt_mem_Cgen k⟩ := by
  rw [packetElt, packetGen_of_lt (k := ⟨k, by omega⟩) k.2]

theorem a0_eq : a0 = Dyadic.a0Elt := by
  have hρ : rhoEquiv qA = rhoEquiv (qElt 17) * rhoEquiv (qElt 10) * rhoEquiv (qElt 5) *
      rhoEquiv (qElt 4) * rhoEquiv (qElt 2) * rhoEquiv (qElt 1) := by
    rw [qA_eq]
    simp only [rhoEquiv_mul, mul_assoc]
  have e : (⟨rhoEquiv qA * hElt 5, Cgen.mul_mem (rhoEquiv_mem_Cgen qA_mem) (hElt_mem_Cgen 5)⟩ :
      Cgen) = ⟨rhoEquiv (qElt 17), rhoEquiv_qElt_mem_Cgen 17⟩ *
        ⟨rhoEquiv (qElt 10), rhoEquiv_qElt_mem_Cgen 10⟩ *
        ⟨rhoEquiv (qElt 5), rhoEquiv_qElt_mem_Cgen 5⟩ *
        ⟨rhoEquiv (qElt 4), rhoEquiv_qElt_mem_Cgen 4⟩ *
        ⟨rhoEquiv (qElt 2), rhoEquiv_qElt_mem_Cgen 2⟩ *
        ⟨rhoEquiv (qElt 1), rhoEquiv_qElt_mem_Cgen 1⟩ * ⟨hElt 5, hElt_mem_Cgen 5⟩ := by
    apply Subtype.ext
    show rhoEquiv qA * hElt 5 = rhoEquiv (qElt 17) * rhoEquiv (qElt 10) * rhoEquiv (qElt 5) *
      rhoEquiv (qElt 4) * rhoEquiv (qElt 2) * rhoEquiv (qElt 1) * hElt 5
    rw [hρ]
  have h1 : packetElt ⟨1, by norm_num⟩ = kappa ⟨rhoEquiv (qElt 1), rhoEquiv_qElt_mem_Cgen 1⟩ :=
    packetElt_kappa_qElt 1
  have h2 : packetElt ⟨2, by norm_num⟩ = kappa ⟨rhoEquiv (qElt 2), rhoEquiv_qElt_mem_Cgen 2⟩ :=
    packetElt_kappa_qElt 2
  have h4 : packetElt ⟨4, by norm_num⟩ = kappa ⟨rhoEquiv (qElt 4), rhoEquiv_qElt_mem_Cgen 4⟩ :=
    packetElt_kappa_qElt 4
  have h5 : packetElt ⟨5, by norm_num⟩ = kappa ⟨rhoEquiv (qElt 5), rhoEquiv_qElt_mem_Cgen 5⟩ :=
    packetElt_kappa_qElt 5
  have h10 : packetElt ⟨10, by norm_num⟩ =
      kappa ⟨rhoEquiv (qElt 10), rhoEquiv_qElt_mem_Cgen 10⟩ := packetElt_kappa_qElt 10
  have h17 : packetElt ⟨17, by norm_num⟩ =
      kappa ⟨rhoEquiv (qElt 17), rhoEquiv_qElt_mem_Cgen 17⟩ := packetElt_kappa_qElt 17
  have h28 : packetElt ⟨28, by norm_num⟩ = kappa ⟨hElt 5, hElt_mem_Cgen 5⟩ := by
    have h := gSeq_six
    rw [gSeq_of_lt (by norm_num)] at h
    exact h
  rw [a0, e, Dyadic.a0Elt, h1, h2, h4, h5, h10, h17, h28]
  simp only [map_mul]

theorem aB_eq : aB = aS gSeq := by
  rw [aB, aS, WB, a0_eq]

theorem WB_eq : WB = (conjWord24.map fun w => op (gSeq (w - 1))).prod := by
  rw [WB, wordS, conjWord0, List.map_map]
  rfl

theorem conjWord_length : conjWord24.length = 24 := by decide +kernel

theorem conjWord_range : ∀ w ∈ conjWord24, 1 ≤ w ∧ w ≤ 26 := by decide +kernel

theorem native_pinned_B_pair_and_intertwiner_data :
    qA = pauliQ (false, 1078, 64) ∧ qA ∈ Subgroup.centralizer {Short.rStar} ∧
    a0 = kappa ⟨rhoEquiv qA * hElt 5, Cgen.mul_mem (rhoEquiv_mem_Cgen qA_mem) (hElt_mem_Cgen 5)⟩ ∧
    gSeq 0 = kappa ⟨rhoEquiv (qElt 1), rhoEquiv_qElt_mem_Cgen 1⟩ ∧
    (∀ i : Fin 24, gSeq (i + 1) = kappa ⟨hElt i, hElt_mem_Cgen i⟩) ∧ gSeq 25 = taubar ∧
    conjWord24.length = 24 ∧ (∀ w ∈ conjWord24, 1 ≤ w ∧ w ≤ 26) ∧
    WB = (conjWord24.map fun w => op (gSeq (w - 1))).prod ∧ aB = WB⁻¹ * op a0 * WB ∧
    bB = op taubar ∧ HB = Subgroup.closure {aB, bB} ∧
    F0mat = Dyadic.rowsK KC.BM.NativePair.F0.rows ∧ Fmat = Dyadic.rowsK KC.BM.NativePair24.F.rows ∧
    Tmat = Dyadic.rowsK KC.BM.NativePair24.T.rows :=
  ⟨rfl, qA_mem, rfl, gSeq_zero, gSeq_succ, gSeq_last, conjWord_length, conjWord_range, WB_eq, rfl,
    rfl, rfl, rfl, pair_file_facts.1, pair_file_facts.2⟩

theorem orderOf_betaRow {β : Cbar →* GL (Fin 4370) (ZMod 2)} (hinj : Function.Injective β)
    (s : Sbp) : orderOf s = orderOf ((betaRow β s : MatBˣ) : MatB) := by
  rw [orderOf_units, orderOf_injective (betaRow β) (betaRow_injective hinj) s]

theorem map_probeProd {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (a b : M) :
    f (probeProd a b) = probeProd (f a) (f b) := by
  unfold probeProd
  rw [map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun l _ => ?_)
  cases l <;> rfl

section Explicit

variable {β : Cbar →* GL (Fin 4370) (ZMod 2)} (hβ : IsExplicitBinary β)

include hβ in
theorem betaRow_a0 : ((betaRow β (op a0) : MatBˣ) : MatB) = F0mat := by
  rw [a0_eq]
  exact hβ.a0

include hβ in
theorem betaRow_aB : ((betaRow β aB : MatBˣ) : MatB) = Fmat := by
  rw [aB_eq]
  exact betaRow_aS β gSeq hβ.gen hβ.a0

include hβ in
theorem betaRow_bB : ((betaRow β bB : MatBˣ) : MatB) = Dyadic.Qmat 25 := by
  rw [bB, ← gSeq_last, hβ.gen 25 (by norm_num), Qn_25]

include hβ in
theorem betaRow_aB_bB :
    ((betaRow β (aB * bB) : MatBˣ) : MatB) = Fmat * Dyadic.Qmat 25 := by
  rw [map_mul, Units.val_mul, betaRow_aB hβ, betaRow_bB hβ]

include hβ in
theorem betaRow_probe :
    ((betaRow β (probeProd aB bB) : MatBˣ) : MatB) = probeProd Fmat (Dyadic.Qmat 25) := by
  have h := map_probeProd ((Units.coeHom MatB).comp (betaRow β)) aB bB
  simp only [MonoidHom.comp_apply, Units.coeHom_apply] at h
  rw [h, betaRow_aB hβ, betaRow_bB hβ]

include hβ in
theorem native_pair_binary_facts :
    ((betaRow β (op a0) : MatBˣ) : MatB) = F0mat ∧ ((betaRow β aB : MatBˣ) : MatB) = Fmat ∧
    ((betaRow β bB : MatBˣ) : MatB) = Dyadic.Qmat 25 ∧
    orderOf (op a0) = 2 ∧ (F0mat - 1).rank = 2158 ∧ orderOf aB = 2 ∧ orderOf bB = 3 ∧
    orderOf (aB * bB) = 55 ∧ orderOf (probeProd aB bB) = 23 := by
  obtain ⟨-, hF0sq, hF0ne, hrk, -, -, hFF, hQ3, hQne, h55, h5, h11, hw, hw23⟩ := pair_matrix_facts
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have hinj := hβ.injective
  refine ⟨betaRow_a0 hβ, betaRow_aB hβ, betaRow_bB hβ, ?_, hrk, ?_, ?_, ?_, ?_⟩
  · rw [orderOf_betaRow hinj, betaRow_a0 hβ]
    exact orderOf_eq_prime (by rw [sq]; exact hF0sq) hF0ne
  · rw [orderOf_betaRow hinj, betaRow_aB hβ]
    refine orderOf_eq_prime (by rw [sq]; exact hFF) fun h => hF0ne ?_
    have hBW := pair_matrix_facts.1
    rw [h, Matrix.mul_one] at hBW
    have hu : IsUnit (BWmat) := by
      rw [← wordQ_conjWord0, ← betaRow_wordS β gSeq hβ.gen conjWord0 conjWord0_lt]
      exact Units.isUnit _
    have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
    calc F0mat = F0mat * BWmat * (BWmat)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      _ = 1 := by rw [← hBW, Matrix.mul_nonsing_inv _ hd]
  · rw [orderOf_betaRow hinj, betaRow_bB hβ]
    exact orderOf_eq_prime hQ3 hQne
  · rw [orderOf_betaRow hinj, betaRow_aB_bB hβ]
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h55 fun p hp hpd => ?_
    have hp' : p = 5 ∨ p = 11 := by
      have h55' : (55 : ℕ) = 5 * 11 := by norm_num
      rw [h55'] at hpd
      rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
    rcases hp' with rfl | rfl
    · exact h11
    · exact h5
  · rw [orderOf_betaRow hinj, betaRow_probe hβ]
    exact orderOf_eq_prime hw23 hw

end Explicit

theorem closure_bA_eq_top :
    Subgroup.closure ({bA₁, bA₂} : Set NativeSporadic.B) = ⊤ := by
  set H := Subgroup.closure ({bA₁, bA₂} : Set NativeSporadic.B)
  have key : ∀ p ∈ NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2,
      ∃ u ∈ H, bMat u = p := by
    intro p hp
    induction hp using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨bA₁, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
      · exact ⟨bA₂, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
    | one => exact ⟨1, H.one_mem, map_one bMat⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      exact ⟨u * v, H.mul_mem hu hv, map_mul bMat u v⟩
  rw [eq_top_iff]
  intro u _
  obtain ⟨v, hv, hvu⟩ := key _ (u : NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1
    NativeSporadic.BSeed2).2
  have : v = u := bMat_injective hvu
  rw [← this]
  exact hv

section Explicit

variable {β : Cbar →* GL (Fin 4370) (ZMod 2)} (hβ : IsExplicitBinary β)

include hβ in
theorem iota_facts :
    ∃ ι : NativeSporadic.B →* Sbp, Function.Injective ι ∧
    (∀ X, ((betaRow β (ι X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹) ∧
    ι bA₁ = aB ∧ ι bA₂ = bB ∧ ι.range = HB := by
  obtain ⟨ι, hι, hιβ⟩ := exists_iota β gSeq hβ.gen hβ.injective gSeq_last aB (betaRow_aB hβ)
  obtain ⟨-, -, -, -, hFT, hQT, -⟩ := pair_matrix_facts
  have h1 : ι bA₁ = aB := by
    apply betaRow_inj hβ.injective
    rw [hιβ, bMat_bA₁, betaRow_aB hβ, ← hFT, Matrix.mul_assoc, Tmat_mul_inv, Matrix.mul_one]
  have h2 : ι bA₂ = bB := by
    apply betaRow_inj hβ.injective
    rw [hιβ, bMat_bA₂, betaRow_bB hβ, ← hQT, Matrix.mul_assoc, Tmat_mul_inv, Matrix.mul_one]
  refine ⟨ι, hι, hιβ, h1, h2, ?_⟩
  rw [MonoidHom.range_eq_map, ← closure_bA_eq_top, MonoidHom.map_closure, Set.image_pair, h1, h2,
    HB]

include hβ in
theorem native_to_pinned_B_exact_simultaneous_intertwiner :
    Tmat.rank = 4370 ∧ Fmat * Tmat = Tmat * genA₁ ∧ Dyadic.Qmat 25 * Tmat = Tmat * genA₂ ∧
    HB.map ((MulAut.conj Tunit⁻¹).toMonoidHom.comp (betaRow β)) =
      (Units.map (NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1
        NativeSporadic.BSeed2).subtype).range ∧
    Tmat⁻¹ * ((betaRow β aB : MatBˣ) : MatB) * Tmat = genA₁ ∧
    Tmat⁻¹ * ((betaRow β bB : MatBˣ) : MatB) * Tmat = genA₂ := by
  obtain ⟨-, -, -, -, hFT, hQT, -⟩ := pair_matrix_facts
  obtain ⟨ι, -, hιβ, h1, h2, hrange⟩ := iota_facts hβ
  have hconj : ∀ X : NativeSporadic.B, Tmat⁻¹ * (Tmat * bMat X * Tmat⁻¹) * Tmat = bMat X := by
    intro X
    calc Tmat⁻¹ * (Tmat * bMat X * Tmat⁻¹) * Tmat = (Tmat⁻¹ * Tmat) * bMat X * (Tmat⁻¹ * Tmat) := by
          simp only [Matrix.mul_assoc]
      _ = bMat X := by rw [Tmat_inv_mul, Matrix.one_mul, Matrix.mul_one]
  refine ⟨Matrix.rank_of_isUnit _ Tmat_isUnit |>.trans (Fintype.card_fin _), hFT, hQT, ?_, ?_, ?_⟩
  · rw [← hrange, MonoidHom.map_range]
    refine congrArg MonoidHom.range (MonoidHom.ext fun X => Units.ext ?_)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      Units.val_mul, Units.coe_map, Submonoid.coe_subtype, coe_Tunit, coe_Tunit_inv, hιβ]
    exact hconj X
  · rw [← h1, hιβ, bMat_bA₁]
    exact hconj bA₁
  · rw [← h2, hιβ, bMat_bA₂]
    exact hconj bA₂

include hβ in
theorem pinned_B_explicit_embedding :
    ∃ ι : NativeSporadic.B →* Sbp, Function.Injective ι ∧
      (∀ X, ((betaRow β (ι X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹) ∧
      ι.range = HB ∧ ι bA₁ = aB ∧ ι bA₂ = bB ∧
      Nontrivial NativeSporadic.B ∧ commutator NativeSporadic.B = ⊤ ∧
      2 * 3 * 5 * 11 * 23 ∣ Nat.card NativeSporadic.B := by
  obtain ⟨ι, hι, hιβ, h1, h2, hrange⟩ := iota_facts hβ
  obtain ⟨-, -, ha2, hb3, hab55, hw23⟩ := (native_pair_binary_facts hβ).2.2.2
  have e1 : orderOf bA₁ = 2 := by rw [← orderOf_injective ι hι, h1]; exact ha2
  have e2 : orderOf bA₂ = 3 := by rw [← orderOf_injective ι hι, h2]; exact hb3
  have e3 : orderOf (bA₁ * bA₂) = 55 := by
    rw [← orderOf_injective ι hι, map_mul, h1, h2]
    exact hab55
  have e4 : orderOf (probeProd bA₁ bA₂) = 23 := by
    rw [← orderOf_injective ι hι, map_probeProd, h1, h2]; exact hw23
  refine ⟨ι, hι, hιβ, hrange, h1, h2, ?_, ?_, ?_⟩
  · refine ⟨⟨bA₁, 1, fun h => ?_⟩⟩
    rw [h, orderOf_one] at e1
    exact absurd e1 (by norm_num)
  ·
    have hα : ∀ x ∈ ({bA₁, bA₂} : Set NativeSporadic.B), Abelianization.of x = 1 := by
      have q1 := pow_orderOf_eq_one bA₁
      have q2 := pow_orderOf_eq_one bA₂
      have q3 := pow_orderOf_eq_one (bA₁ * bA₂)
      rw [e1] at q1
      rw [e2] at q2
      rw [e3] at q3
      have p1 : Abelianization.of bA₁ ^ 2 = 1 := by rw [← map_pow, q1, map_one]
      have p2 : Abelianization.of bA₂ ^ 3 = 1 := by rw [← map_pow, q2, map_one]
      have p3 : (Abelianization.of bA₁ * Abelianization.of bA₂) ^ 55 = 1 := by
        rw [← map_mul, ← map_pow, q3, map_one]
      set x := Abelianization.of bA₁
      set y := Abelianization.of bA₂
      have p6 : (x * y) ^ 6 = 1 := by
        rw [mul_pow, show 6 = 2 * 3 by norm_num, pow_mul, p1, one_pow, one_mul, pow_mul', p2,
          one_pow]
      have hxy : x * y = 1 := by
        have := (pow_gcd_eq_one (a := x * y) (m := 6) (n := 55)).2 ⟨p6, p3⟩
        rwa [show Nat.gcd 6 55 = 1 by norm_num, pow_one] at this
      have hy : y = x⁻¹ := eq_inv_of_mul_eq_one_right hxy
      have hx3 : x ^ 3 = 1 := by
        rw [hy, inv_pow] at p2
        exact inv_eq_one.1 p2
      have hx : x = 1 := by
        have := (pow_gcd_eq_one (a := x) (m := 2) (n := 3)).2 ⟨p1, hx3⟩
        rwa [show Nat.gcd 2 3 = 1 by norm_num, pow_one] at this
      intro z hz
      rcases hz with rfl | rfl
      · exact hx
      · show y = 1
        rw [hy, hx, inv_one]
    have hle : (⊤ : Subgroup NativeSporadic.B) ≤ Abelianization.of.ker := by
      rw [← closure_bA_eq_top, Subgroup.closure_le]
      intro z hz
      exact hα z hz
    rw [Abelianization.ker_of] at hle
    exact eq_top_iff.2 hle
  · have d1 : 2 ∣ Nat.card NativeSporadic.B := e1 ▸ orderOf_dvd_natCard bA₁
    have d2 : 3 ∣ Nat.card NativeSporadic.B := e2 ▸ orderOf_dvd_natCard bA₂
    have d3 : 55 ∣ Nat.card NativeSporadic.B := e3 ▸ orderOf_dvd_natCard (bA₁ * bA₂)
    have d4 : 23 ∣ Nat.card NativeSporadic.B := e4 ▸ orderOf_dvd_natCard (probeProd bA₁ bA₂)
    have d12 : 2 * 3 ∣ Nat.card NativeSporadic.B :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1 d2
    have d123 : 2 * 3 * 55 ∣ Nat.card NativeSporadic.B :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d12 d3
    have d1234 : 2 * 3 * 55 * 23 ∣ Nat.card NativeSporadic.B :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d123 d4
    exact (show 2 * 3 * 5 * 11 * 23 = 2 * 3 * 55 * 23 by norm_num) ▸ d1234

include hβ in
theorem pinned_B_explicit_native_isomorphism :
    HB = ⊤ ∧ ∃ e : NativeSporadic.B ≃* Sbp,
      (∀ X, ((betaRow β (e X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹) ∧
      e bA₁ = aB ∧ e bA₂ = bB ∧ IsSimpleGroup NativeSporadic.B := by
  obtain ⟨ι, hι, hιβ, h1, h2, hrange⟩ := iota_facts hβ
  have hsurj :=
    iota_surjective β hβ.injective gSeq hβ.gen gSeq_last gSeq_zero_mem gSeq_mem_Jbar ι hιβ
  refine ⟨?_, MulEquiv.ofBijective ι ⟨hι, hsurj⟩, hιβ, h1, h2, isSimpleGroup_B_of_explicit hβ⟩
  rw [← hrange]
  exact MonoidHom.range_eq_top.2 hsurj

end Explicit

end CFSG.Monster.B
