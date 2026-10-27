module

public import CFSG.RankThree.PartOne.DISTX.Row9Perm
public import CFSG.RankThree.PartOne.S12.Sec138Trans
public import CFSG.RankThree.PartOne.S12.InvolAbelian
public import CFSG.RankThree.PartOne.S12.Sec136
public import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.DISTX

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open Equiv

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem conj_mem_reflectionSet_of_mem_torusImage (h : Sec12Hyp G p A c L E) {g t : MulAut E}
    (hg : g ∈ torusImage E L) (ht : t ∈ reflectionSet p E) : g * t * g⁻¹ ∈ reflectionSet p E := by
  obtain ⟨w, -, hw, rfl⟩ := Sec12Three.mem_torusImage_iff.mp hg
  exact conj_mem_reflectionSet h.prime ht hw

theorem row9_hyps (h : Sec12Hyp G p A c L E) (hD3 : ThreeTranspD p E)
    (hclosure : torusImage E L =
      Subgroup.closure (reflectionSet p E ∩ (torusImage E L : Set (MulAut E)))) :
    (∀ x ∈ {x : ↥(torusImage E L) | (x : MulAut E) ∈ reflectionSet p E}, x * x = 1 ∧ x ≠ 1) ∧
    (∀ (g x : ↥(torusImage E L)), x ∈ {x : ↥(torusImage E L) | (x : MulAut E) ∈ reflectionSet p E} →
      g * x * g⁻¹ ∈ {x : ↥(torusImage E L) | (x : MulAut E) ∈ reflectionSet p E}) ∧
    Subgroup.closure {x : ↥(torusImage E L) | (x : MulAut E) ∈ reflectionSet p E} = ⊤ ∧
    (∀ x ∈ {x : ↥(torusImage E L) | (x : MulAut E) ∈ reflectionSet p E},
      ∀ y ∈ {x : ↥(torusImage E L) | (x : MulAut E) ∈ reflectionSet p E},
        orderOf (x * y) ≤ 3) := by
  refine ⟨fun x hx => ?_, fun g x hx => ?_, ?_, fun x hx y hy => ?_⟩
  · refine ⟨Subtype.ext ?_, fun h1 => ?_⟩
    · exact RefFacts.mul_self_eq_one hx.1
    · have := hx.1.1
      rw [show (x : MulAut E) = 1 from congrArg Subtype.val h1, orderOf_one] at this
      omega
  · exact conj_mem_reflectionSet_of_mem_torusImage h g.2 hx
  · set Γ := torusImage E L with hΓ
    have h1 : (Subgroup.closure {x : ↥Γ | (x : MulAut E) ∈ reflectionSet p E}).map Γ.subtype =
        Subgroup.closure (reflectionSet p E ∩ (Γ : Set (MulAut E))) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, x.2⟩
      · rintro ⟨hy, hyΓ⟩
        exact ⟨⟨y, hyΓ⟩, hy, rfl⟩
    rw [← hclosure] at h1
    apply Subgroup.map_injective Γ.subtype_injective
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  · rw [← Subgroup.orderOf_coe (x * y)]
    exact hD3 _ hx _ hy

theorem row9_conj (h : Sec12Hyp G p A c L E) (hD3 : ThreeTranspD p E)
    (hclosure : torusImage E L =
      Subgroup.closure (reflectionSet p E ∩ (torusImage E L : Set (MulAut E))))
    (ψ : ↥(torusImage E L) ≃* Perm (Fin 4)) {x y : MulAut E} (hx : x ∈ reflectionSet p E)
    (hxΓ : x ∈ torusImage E L) (hy : y ∈ reflectionSet p E) (hyΓ : y ∈ torusImage E L) :
    ∃ g ∈ torusImage E L, g * x * g⁻¹ = y := by
  obtain ⟨h1, h2, h3, h4⟩ := row9_hyps h hD3 hclosure
  obtain ⟨g, hg⟩ := exists_conj_of_mem ψ _ h1 h2 h3 h4 (x := ⟨x, hxΓ⟩) (y := ⟨y, hyΓ⟩) hx hy
  exact ⟨g, g.2, congrArg Subtype.val hg⟩

theorem row9_commute_cases (h : Sec12Hyp G p A c L E) (hD3 : ThreeTranspD p E)
    (hclosure : torusImage E L =
      Subgroup.closure (reflectionSet p E ∩ (torusImage E L : Set (MulAut E))))
    (ψ : ↥(torusImage E L) ≃* Perm (Fin 4)) {t y : MulAut E} (ht : t ∈ reflectionSet p E)
    (htΓ : t ∈ torusImage E L) (hy : y ∈ reflectionSet p E) (hyΓ : y ∈ torusImage E L)
    (hcomm : y * t = t * y) :
    y = t ∨ ∃ x ∈ reflectionSet p E, x ∈ torusImage E L ∧ ∃ z ∈ reflectionSet p E,
      z ∈ torusImage E L ∧ x * t ≠ t * x ∧ z * t ≠ t * z ∧ y = x * z * x⁻¹ := by
  obtain ⟨h1, h2, h3, h4⟩ := row9_hyps h hD3 hclosure
  have hcomm' : (⟨y, hyΓ⟩ : ↥(torusImage E L)) * ⟨t, htΓ⟩ = ⟨t, htΓ⟩ * ⟨y, hyΓ⟩ :=
    Subtype.ext hcomm
  rcases exists_cases_of_commute ψ _ h1 h2 h3 h4 (t := ⟨t, htΓ⟩) (y := ⟨y, hyΓ⟩) ht hy hcomm' with
    hyt | ⟨x, hx, z, hz, hxt, hzt, hyxz⟩
  · exact Or.inl (congrArg Subtype.val hyt)
  · refine Or.inr ⟨x, hx, x.2, z, hz, z.2, fun h' => hxt (Subtype.ext h'), fun h' => hzt
  (Subtype.ext h'),
      congrArg Subtype.val hyxz⟩

omit [Finite G] in
theorem pow_mul_eq_one_of_movedS_eq {M : Type*} [CommGroup M] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : ∀ x : M, x ^ p = 1) {s d : MulAut M} (hs : s * s = 1) (hd : d * d = 1)
    (hmov : Invol.movedS s = Invol.movedS d) : (s * d) ^ p = 1 := by
  set C := Invol.invS s with hC
  have hCd : Invol.invS d = C := by
    rw [← Invol.movedS_eq_invS hp hp2 hpow hd, ← hmov, Invol.movedS_eq_invS hp hp2 hpow hs]
  have hsC : ∀ x ∈ C, s x = x⁻¹ := fun x hx => hx
  have hdC : ∀ x ∈ C, d x = x⁻¹ := fun x hx => by
    have : x ∈ Invol.invS d := hCd ▸ hx
    exact this
  have hρs : ∀ e : M, s e * e⁻¹ ∈ C := fun e => by
    rw [hC, ← Invol.movedS_eq_invS hp hp2 hpow hs]
    exact Subgroup.subset_closure ⟨e, rfl⟩
  have hρd : ∀ e : M, d e * e⁻¹ ∈ C := fun e => by
    rw [← hCd, ← Invol.movedS_eq_invS hp hp2 hpow hd]
    exact Subgroup.subset_closure ⟨e, rfl⟩
  set f : M → M := fun e => (s e * e⁻¹) * (d e * e⁻¹)⁻¹ with hf
  have hfC : ∀ e, f e ∈ C := fun e => C.mul_mem (hρs e) (C.inv_mem (hρd e))
  have hsd : ∀ e : M, (s * d) e = f e * e := by
    intro e
    have h1 : d e = (d e * e⁻¹) * e := by group
    have h2 : s (d e * e⁻¹) = (d e * e⁻¹)⁻¹ := hsC _ (hρd e)
    calc (s * d) e = s (d e) := rfl
      _ = s ((d e * e⁻¹) * e) := by rw [← h1]
      _ = (d e * e⁻¹)⁻¹ * s e := by rw [map_mul, h2]
      _ = f e * e := by
        have h3 : s e = (s e * e⁻¹) * e := by group
        calc (d e * e⁻¹)⁻¹ * s e = (d e * e⁻¹)⁻¹ * ((s e * e⁻¹) * e) := by rw [← h3]
          _ = ((s e * e⁻¹) * (d e * e⁻¹)⁻¹) * e := by ac_rfl
  have hfix : ∀ x ∈ C, (s * d) x = x := fun x hx => by
    show s (d x) = x
    rw [hdC x hx, map_inv, hsC x hx, inv_inv]
  have hpowsd : ∀ (n : ℕ) (e : M), ((s * d) ^ n) e = f e ^ n * e := by
    intro n e
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix _ (hfC e), hsd e]
      group
  refine MulEquiv.ext fun e => ?_
  rw [hpowsd, hpow (f e), one_mul]
  rfl

theorem autMovedInG_eq_zpowers (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hcard : Nat.card E = p ^ 4)
    (hno11 : ¬ (RowModel p L 11 ∧ RowWeylIso E (torusImage E L) 11)) {u : MulAut E}
    (hu : u ∈ reflectionSet p E) (huΓ : ∀ g ∈ torusImage E L, u * g = g * u) :
    autMovedInG E u = Subgroup.zpowers c := by
  have hp := h.prime
  have hcE : c ∈ E := h.A_le_E h.c_mem
  obtain ⟨-, -, hcardB⟩ := hF13.reflection u hu
  set B := autMovedInG E u with hB
  have hle : B ≤ E := Subgroup.map_subtype_le _
  have hinv : torusInvariant E L B := by
    rintro w ⟨hwL, hwN⟩ b hb
    have hwN' : w ∈ Subgroup.normalizer (E : Set G) := hwN
    have hg := Sec138Trans.conjAut_mem_torusImage hwN' hwL
    have h1 : conjAut E w hwN' * u * (conjAut E w hwN')⁻¹ = u := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (huΓ _ hg).symm
    have h2 := Equivariance.autMovedInG_conj u hwN'
    rw [h1] at h2
    have h3 : w * b * w⁻¹ ∈ conjBy w (autMovedInG E u) :=
      Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom hb
    rw [← h2] at h3
    exact h3
  have hp1 : 1 < p := hp.one_lt
  have hne : B ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hcardB
    omega
  have hne' : B ≠ E := fun h0 => by
    rw [h0, hcard] at hcardB
    have : p ^ 4 = p * p ^ 3 := by ring
    have h5 : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp1
    nlinarith
  rcases hF.four.1 B hle hinv hne hne' with hB1 | hB1
  · exact hB1
  · exfalso
    rcases hF.four.2 with ⟨hsup, hinf⟩ | ⟨h11, -⟩
    · set V := ⁅E, L ⊓ torusNormalizer E⁆ with hV
      have hVE : V ≤ E := hB1 ▸ hle
      have hcV : c ∉ V := fun hc => h.c_ne_one (by
        have : c ∈ Subgroup.zpowers c ⊓ V := ⟨Subgroup.mem_zpowers c, hc⟩
        rwa [hinf, Subgroup.mem_bot] at this)
      have hcomm : ∀ e ∈ V, e * c = c * e := fun e he =>
        congrArg Subtype.val (h.E_elem.is_comm.comm (⟨e, hVE he⟩ : ↥E) ⟨c, hcE⟩)
      have hcardsup := Planes.card_sup_zpowers hp V (Sec12Three.pow_eq_one_of_mem_E h hcE) hcV hcomm
      rw [sup_comm, ← hsup, hcard, ← hB1, hcardB] at hcardsup
      have h5 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp1
      have : p ^ 4 = p * p ^ 3 := by ring
      nlinarith
    · exact hno11 h11

theorem eq_of_centralizes (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hD3 : ThreeTranspD p E) (hcard : Nat.card E = p ^ 4)
    (hno11 : ¬ (RowModel p L 11 ∧ RowWeylIso E (torusImage E L) 11)) {s d : MulAut E}
    (hs : s ∈ reflectionSet p E) (hd : d ∈ reflectionSet p E)
    (hsΓ : ∀ g ∈ torusImage E L, s * g = g * s) (hdΓ : ∀ g ∈ torusImage E L, d * g = g * d) :
    s = d := by
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => h.E_elem.is_comm.comm a b
  let _inst : CommGroup ↥E := commGroupOf hEc
  have hpow : ∀ x : ↥E, x ^ p = 1 := fun x =>
    Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h x.2)
  have hs2 : s * s = 1 := RefFacts.mul_self_eq_one hs.1
  have hd2 : d * d = 1 := RefFacts.mul_self_eq_one hd.1
  have hms := autMovedInG_eq_zpowers h hF hF13 hcard hno11 hs hsΓ
  have hmd := autMovedInG_eq_zpowers h hF hF13 hcard hno11 hd hdΓ
  have hmov : Invol.movedS s = Invol.movedS d := by
    apply Subgroup.map_injective E.subtype_injective
    exact hms.trans hmd.symm
  have hpowsd := pow_mul_eq_one_of_movedS_eq hp hp2 hpow hs2 hd2 hmov
  have hdvd : orderOf (s * d) ∣ p := orderOf_dvd_of_pow_eq_one hpowsd
  have hle3 : orderOf (s * d) ≤ 3 := hD3 s hs d hd
  have hord : orderOf (s * d) = 1 := by
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact h1
    · omega
  have hsd : s * d = 1 := orderOf_eq_one_iff.mp hord
  calc s = s * (d * d) := by rw [hd2, mul_one]
    _ = (s * d) * d := by rw [mul_assoc]
    _ = d := by rw [hsd, one_mul]

theorem exists_partner (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hD3 : ThreeTranspD p E) (hTr : TransitiveD p E)
    (hcard : Nat.card E = p ^ 4)
    (hno11 : ¬ (RowModel p L 11 ∧ RowWeylIso E (torusImage E L) 11))
    (hclosure : torusImage E L =
      Subgroup.closure (reflectionSet p E ∩ (torusImage E L : Set (MulAut E))))
    (ψ : ↥(torusImage E L) ≃* Perm (Fin 4)) {t d : MulAut E} (ht : t ∈ reflectionSet p E)
    (htΓ : t ∈ torusImage E L) (hd : d ∈ reflectionSet p E) (hcomm : d * t = t * d)
    (hne : d ≠ t) : ∃ s ∈ reflectionSet p E, s * t ≠ t * s ∧ s * d ≠ d * s := by
  by_contra H
  push Not at H
  have hdR : ∀ y ∈ reflectionSet p E, y ∈ torusImage E L → d * y = y * d := by
    intro y hy hyΓ
    by_cases hyt : y * t = t * y
    · rcases row9_commute_cases h hD3 hclosure ψ ht htΓ hy hyΓ hyt with hyt' |
        ⟨x, hx, hxΓ, z, hz, hzΓ, hxt, hzt, hyxz⟩
      · rw [hyt']
        exact hcomm
      · have hxd : Commute x d := H x hx hxt
        have hzd : Commute z d := H z hz hzt
        rw [hyxz]
        exact ((hxd.mul_left hzd).mul_left hxd.inv_left).symm
    · exact (H y hy hyt).symm
  have hdΓ : ∀ g ∈ torusImage E L, d * g = g * d := by
    have hle : torusImage E L ≤ Subgroup.centralizer ({d} : Set (MulAut E)) := by
      calc torusImage E L
          = Subgroup.closure (reflectionSet p E ∩ (torusImage E L : Set (MulAut E))) := hclosure
        _ ≤ _ := (Subgroup.closure_le _).mpr fun y hy =>
          Subgroup.mem_centralizer_singleton_iff.mpr (hdR y hy.1 hy.2).symm
    exact fun g hg => (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm
  obtain ⟨s₀, hs₀, hs₀d⟩ : ∃ s₀ ∈ reflectionSet p E, s₀ * d ≠ d * s₀ := by
    by_contra hall
    push Not at hall
    obtain ⟨x, hx, hxt⟩ := hTr d hd t ht
    have hxd : x * d = d * x := by
      have hle : reflectionGroup p E ≤ Subgroup.centralizer ({d} : Set (MulAut E)) :=
        (Subgroup.closure_le _).mpr fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hall y
        hy)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    have htd : t = d := by rw [← hxt, hxd, mul_inv_cancel_right]
    exact hne htd.symm
  have hs₀Γ : ¬ ∀ g ∈ torusImage E L, s₀ * g = g * s₀ := fun hcent =>
    hs₀d (by rw [eq_of_centralizes h hF hF13 hD3 hcard hno11 hs₀ hd hcent hdΓ])
  obtain ⟨y, hy, hyΓ, hys⟩ : ∃ y ∈ reflectionSet p E, y ∈ torusImage E L ∧ y * s₀ ≠ s₀ * y := by
    by_contra hno
    push Not at hno
    apply hs₀Γ
    intro g hg
    have hle : torusImage E L ≤ Subgroup.centralizer ({s₀} : Set (MulAut E)) := by
      calc torusImage E L
          = Subgroup.closure (reflectionSet p E ∩ (torusImage E L : Set (MulAut E))) := hclosure
        _ ≤ _ := (Subgroup.closure_le _).mpr fun y hy' =>
          Subgroup.mem_centralizer_singleton_iff.mpr (hno y hy'.1 hy'.2)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm
  obtain ⟨g, hgΓ, hgy⟩ := row9_conj h hD3 hclosure ψ hy hyΓ ht htΓ
  have hs' : g * s₀ * g⁻¹ ∈ reflectionSet p E :=
    conj_mem_reflectionSet_of_mem_torusImage h hgΓ hs₀
  have hnt : (g * s₀ * g⁻¹) * t ≠ t * (g * s₀ * g⁻¹) := by
    intro h'
    apply hys
    rw [← hgy] at h'
    have h6 : g * (s₀ * y) * g⁻¹ = g * (y * s₀) * g⁻¹ := by
      calc g * (s₀ * y) * g⁻¹ = g * s₀ * g⁻¹ * (g * y * g⁻¹) := by group
        _ = g * y * g⁻¹ * (g * s₀ * g⁻¹) := h'
        _ = g * (y * s₀) * g⁻¹ := by group
    exact (mul_left_cancel (mul_right_cancel h6)).symm
  have hnd := H _ hs' hnt
  apply hs₀d
  have hgd : g * d * g⁻¹ = d := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hdΓ g hgΓ).symm
  have h5 : g * (s₀ * d) * g⁻¹ = g * (d * s₀) * g⁻¹ := by
    calc g * (s₀ * d) * g⁻¹ = (g * s₀ * g⁻¹) * (g * d * g⁻¹) := by group
      _ = (g * s₀ * g⁻¹) * d := by rw [hgd]
      _ = d * (g * s₀ * g⁻¹) := hnd
      _ = (g * d * g⁻¹) * (g * s₀ * g⁻¹) := by rw [hgd]
      _ = g * (d * s₀) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h5)

end CFSG.RankThree.PartOne.DISTX
