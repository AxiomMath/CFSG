module

public import CFSG.Quasithin.H13.L32NLem14325k

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.Vol2.Ch10.SecF

namespace L14325

section Klein

variable {M : Type*} [CommGroup M] [Finite M]

theorem klein_cases (h4 : Nat.card M = 4) (hsq : ∀ m : M, m * m = 1) {w u : M} (hw : w ≠ 1)
    (hu : u ≠ 1) (huw : u ≠ w) (m : M) : m = 1 ∨ m = w ∨ m = u ∨ m = w * u := by
  classical
  have := Fintype.ofFinite M
  have hwu1 : w * u ≠ 1 := fun h => huw (by
    calc u = w * w * u := by rw [hsq, one_mul]
      _ = w := by rw [mul_assoc, h, mul_one])
  have hwuw : w * u ≠ w := fun h => hu (by
    calc u = w⁻¹ * (w * u) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have hwuu : w * u ≠ u := fun h => hw (by
    calc w = w * u * u⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  have h1 : (1 : M) ∉ ({w, u, w * u} : Finset M) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hw.symm, hu.symm, hwu1.symm⟩
  have h2 : w ∉ ({u, w * u} : Finset M) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨huw.symm, hwuw.symm⟩
  have h3 : u ∉ ({w * u} : Finset M) := by
    simp only [Finset.mem_singleton]
    exact hwuu.symm
  have hcard : ({1, w, u, w * u} : Finset M).card = 4 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have huniv : ({1, w, u, w * u} : Finset M) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, ← Nat.card_eq_fintype_card, h4])
  have hm : m ∈ ({1, w, u, w * u} : Finset M) := huniv ▸ Finset.mem_univ m
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

omit [Finite M] in
theorem mulAut_pow_three_apply (α : MulAut M) (m : M) : (α ^ 3) m = α (α (α m)) := by
  rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply]

theorem klein_fix (h4 : Nat.card M = 4) (hsq : ∀ m : M, m * m = 1) {α : MulAut M}
    (h3 : α ^ 3 = 1) {w : M} (hw : w ≠ 1) (hαw : α w = w) : α = 1 := by
  ext u
  rw [MulAut.one_apply]
  by_cases hu : u = 1
  · rw [hu, map_one]
  by_cases huw : u = w
  · rw [huw, hαw]
  have hα1 : α u ≠ 1 := (MulEquiv.map_ne_one_iff α).mpr hu
  have hαw' : α u ≠ w := fun h => huw (α.injective (h.trans hαw.symm))
  rcases klein_cases h4 hsq hw hu huw (α u) with h | h | h | h
  · exact absurd h hα1
  · exact absurd h hαw'
  · exact h
  · exfalso
    have h2 : α (w * u) = u := by rw [map_mul, hαw, h, ← mul_assoc, hsq, one_mul]
    have h3u := mulAut_pow_three_apply α u
    rw [h3, MulAut.one_apply, h, h2, h] at h3u
    apply hw
    calc w = w * u * u⁻¹ := by group
      _ = 1 := by rw [← h3u, mul_inv_cancel]

end Klein

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

omit [Finite G] in
theorem conj_mem_cHat {h e : G} (hh : h ∈ l32nH T V) (he : e ∈ l32nCHat T V) :
    h * e * h⁻¹ ∈ l32nCHat T V := by
  obtain ⟨heH, heN, hec⟩ := he
  refine ⟨(l32nH T V).mul_mem ((l32nH T V).mul_mem hh heH) ((l32nH T V).inv_mem hh),
    L14332.l32nH_le_normalizer_zU ((l32nH T V).mul_mem ((l32nH T V).mul_mem hh heH)
      ((l32nH T V).inv_mem hh)), fun u hu => ?_⟩
  have hu' : h⁻¹ * u * h ∈ fsuU T V := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      (L14332.l32nH_le_normalizer_fsuU T V ((l32nH T V).inv_mem hh)) u).mp hu
  have h1 := hec _ hu'
  have h2 : h * (e * (h⁻¹ * u * h) * e⁻¹ * (h⁻¹ * u * h)⁻¹) * h⁻¹ ∈ centerOf (fsuU T V) :=
    CtxI.conj_mem_zU hh h1
  have e1 : h * (e * (h⁻¹ * u * h) * e⁻¹ * (h⁻¹ * u * h)⁻¹) * h⁻¹ =
      h * e * h⁻¹ * u * (h * e * h⁻¹)⁻¹ * u⁻¹ := by group
  rwa [e1] at h2

namespace CtxI.TransData

variable {C : CtxI G T L V V₂ g D} {x c : G} (X : TransData C x c)
include X

theorem conj_x_mem {h' : G} (hh' : h' ∈ l32nH T V) : h' * x * h'⁻¹ ∈ kI T V g :=
  mem_conjClosure hh' X.x_mem

theorem cent_of_comm {h : G} (hh : h ∈ l32nH T V)
    (hcomm : ∀ h' ∈ l32nH T V, h * (h' * x * h'⁻¹) * h⁻¹ * (h' * x * h'⁻¹)⁻¹ ∈
      Subgroup.centralizer (vP T V c : Set G)) :
    h ∈ Subgroup.centralizer (vP T V c : Set G) := by
  have hfix : ∀ h' ∈ l32nH T V, h * (h' * c * h'⁻¹) * h⁻¹ = h' * c * h'⁻¹ := by
    intro h' hh'
    obtain ⟨v₀, hv₀, hv₀c⟩ := X.exists_move
    have hv : h' * v₀ * h'⁻¹ ∈ vP T V c := conj_mem_vP hh' hv₀
    have hxv : (h' * x * h'⁻¹) * (h' * v₀ * h'⁻¹) * (h' * x * h'⁻¹)⁻¹ * (h' * v₀ * h'⁻¹)⁻¹ =
        h' * c * h'⁻¹ := by
      rw [← hv₀c]
      group
    have hq := hcomm h' hh'
    have hhv : h * (h' * v₀ * h'⁻¹) * h⁻¹ ∈ vP T V c := conj_mem_vP hh hv
    have hx'H : h' * x * h'⁻¹ ∈ l32nH T V :=
      (l32nH T V).mul_mem ((l32nH T V).mul_mem hh' X.x_H) ((l32nH T V).inv_mem hh')
    have hx'hv := conj_mem_vP hx'H hhv
    set q := h * (h' * x * h'⁻¹) * h⁻¹ * (h' * x * h'⁻¹)⁻¹ with hqdef
    set x' := h' * x * h'⁻¹ with hx'
    set w := h * (h' * v₀ * h'⁻¹) * h⁻¹ with hw
    have hqc : (x' * w * x'⁻¹) * q = q * (x' * w * x'⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hq _ hx'hv
    have key : h * (h' * c * h'⁻¹) * h⁻¹ = x' * w * x'⁻¹ * w⁻¹ := by
      calc h * (h' * c * h'⁻¹) * h⁻¹ =
            (q * x') * w * (q * x')⁻¹ * w⁻¹ := by
              rw [← hxv, hqdef, hw]
              group
        _ = q * (x' * w * x'⁻¹) * q⁻¹ * w⁻¹ := by group
        _ = (x' * w * x'⁻¹) * q * q⁻¹ * w⁻¹ := by rw [← hqc]
        _ = x' * w * x'⁻¹ * w⁻¹ := by group
    rcases X.comm_conj hh' (C.ctx.vH_le (X.vP_le hhv)) with h1 | h1
    · exfalso
      apply X.c_ne
      have h2 : h * (h' * c * h'⁻¹) * h⁻¹ = 1 := by rw [key]; exact h1
      calc c = h'⁻¹ * (h⁻¹ * (h * (h' * c * h'⁻¹) * h⁻¹) * h) * h' := by group
        _ = 1 := by rw [h2]; group
    · rw [key]
      exact h1
  have hle : vP T V c ≤ Subgroup.centralizer ({h} : Set G) := conjClosure_le fun h' hh' z hz => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : Commute h (h' * c * h'⁻¹) := by
      show h * (h' * c * h'⁻¹) = h' * c * h'⁻¹ * h
      calc h * (h' * c * h'⁻¹) = (h * (h' * c * h'⁻¹) * h⁻¹) * h := by group
        _ = h' * c * h'⁻¹ * h := by rw [hfix h' hh']
    have := (hc.zpow_right k).eq
    rw [conj_zpow] at this
    exact this.symm
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv))

theorem cent_of_cHat (h64 : G64.LemmaG64) {e : G} (he : e ∈ l32nCHat T V) :
    e ∈ Subgroup.centralizer (vP T V c : Set G) := by
  have heH : e ∈ l32nH T V := he.1
  refine X.cent_of_comm heH fun h' hh' => ?_
  have hx'K := X.conj_x_mem hh'
  have hx'H := C.kI_le hx'K
  refine X.cent_of_hat h64 ((kI T V g).mul_mem ((Subgroup.mem_normalizer_iff.mp
    (le_normalizer_kI heH) _).mp hx'K) ((kI T V g).inv_mem hx'K)) ?_
  have h1 : (h' * x * h'⁻¹) * e⁻¹ * (h' * x * h'⁻¹)⁻¹ ∈ l32nCHat T V :=
    conj_mem_cHat hx'H ((l32nCHat T V).inv_mem he)
  have h2 := (l32nCHat T V).mul_mem he h1
  have e1 : e * ((h' * x * h'⁻¹) * e⁻¹ * (h' * x * h'⁻¹)⁻¹) =
      e * (h' * x * h'⁻¹) * e⁻¹ * (h' * x * h'⁻¹)⁻¹ := by group
  rwa [e1] at h2

theorem exists_y (h64 : G64.LemmaG64) : ∃ y ∈ kI T V g,
    y ^ 3 ∈ Subgroup.centralizer (vP T V c : Set G) ∧
      y ∉ Subgroup.centralizer (vP T V c : Set G) ∧
      ∃ hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G), D.ρ ⟨y, hyN⟩ ^ 3 = 1 ∧
        D.ρ ⟨y, hyN⟩ ≠ 1 := by
  obtain ⟨y, hyK, -, -, hyN, hy3, hy1⟩ := C.exists_three
  have hyH := C.kI_le hyK
  refine ⟨y, hyK, ?_, fun hyc => hy1 ((L14332.rho_eq_one_iff_mem hyH hyN).mpr
    (C.mem_cHat_of_mem_centralizer hyK (X.cent_vH hyK hyc))), hyN, hy3, hy1⟩
  have hy3K : y ^ 3 ∈ kI T V g := (kI T V g).pow_mem hyK 3
  have hy3N : y ^ 3 ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    (Subgroup.normalizer _).pow_mem hyN 3
  have e1 : (⟨y ^ 3, hy3N⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨y, hyN⟩ ^ 3 := rfl
  have hρ : D.ρ ⟨y ^ 3, hy3N⟩ = 1 := by rw [e1, map_pow, hy3]
  exact X.cent_of_hat h64 hy3K ((L14332.rho_eq_one_iff_mem (C.kI_le hy3K) hy3N).mp hρ)

theorem card_intMod (h64 : G64.LemmaG64) : Nat.card (IntMod (vP T V c) X.elem) = 4 :=
  X.card_vP h64

theorem sq_intMod (m : IntMod (vP T V c) X.elem) : m * m = 1 := by
  rw [← pow_two]
  exact IntMod.sq_eq_one m

theorem convI_pow_three {y : G} (hyN : y ∈ Subgroup.normalizer (vP T V c : Set G))
    (hy3 : y ^ 3 ∈ Subgroup.centralizer (vP T V c : Set G)) : convI X.elem ⟨y, hyN⟩ ^ 3 = 1 := by
  rw [← map_pow]
  exact (convI_eq_one_iff X.elem _).mpr hy3

theorem eq_one_of_fix (h64 : G64.LemmaG64) {y : G}
    (hyN : y ∈ Subgroup.normalizer (vP T V c : Set G))
    (hy3 : y ^ 3 ∈ Subgroup.centralizer (vP T V c : Set G))
    (hy1 : y ∉ Subgroup.centralizer (vP T V c : Set G)) {w : G} (hw : w ∈ vP T V c)
    (hyw : y * w * y⁻¹ = w) : w = 1 := by
  by_contra hw1
  apply hy1
  rw [← convI_eq_one_iff X.elem ⟨y, hyN⟩]
  refine klein_fix (X.card_intMod h64) X.sq_intMod (X.convI_pow_three hyN hy3)
    (w := IntMod.mk X.elem ⟨w, hw⟩) (fun h => hw1 (congrArg IntMod.val h)) ?_
  apply IntMod.val_injective
  rw [convI_apply_val]
  exact hyw

theorem eq_one_of_cent (h64 : G64.LemmaG64) {w : G} (hw : w ∈ vP T V c)
    (hwK : ∀ k ∈ kI T V g, k * w * k⁻¹ = w) : w = 1 := by
  obtain ⟨y, hyK, hy3, hy1, -⟩ := X.exists_y h64
  exact X.eq_one_of_fix h64 (H_le_normalizer_vP c (C.kI_le hyK)) hy3 hy1 hw (hwK y hyK)

end CtxI.TransData

end L14325

end CFSG.Quasithin.H13
