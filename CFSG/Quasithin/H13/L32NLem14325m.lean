module

public import CFSG.Quasithin.H13.L32NLem14325l

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.Vol2.Ch10.SecF

namespace L14325

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

omit [Finite G] in
theorem conj_eq_of_odd {y w : G} {m k : ℕ} (hm : Odd m) (hym : y ^ m = 1)
    (hyd : y * (y * w * y⁻¹ * w⁻¹) * y⁻¹ = y * w * y⁻¹ * w⁻¹)
    (hd : (y * w * y⁻¹ * w⁻¹) ^ (2 ^ k) = 1) : y * w * y⁻¹ = w := by
  set d := y * w * y⁻¹ * w⁻¹ with hdd
  have hpow : ∀ j : ℕ, y ^ j * w * (y ^ j)⁻¹ = d ^ j * w := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hydj : y * d ^ j * y⁻¹ = d ^ j := by
        have := map_pow (MulAut.conj y) d j
        simp only [MulAut.conj_apply] at this
        rw [this, hyd]
      calc y ^ (j + 1) * w * (y ^ (j + 1))⁻¹ = y * (y ^ j * w * (y ^ j)⁻¹) * y⁻¹ := by
            rw [pow_succ']; group
        _ = y * (d ^ j * w) * y⁻¹ := by rw [ih]
        _ = (y * d ^ j * y⁻¹) * (y * w * y⁻¹) := by group
        _ = d ^ j * (d * w) := by rw [hydj, hdd]; group
        _ = d ^ (j + 1) * w := by rw [pow_succ]; group
  have h1 := hpow m
  rw [hym] at h1
  have hdm : d ^ m = 1 := by
    have : w = d ^ m * w := by simpa using h1
    calc d ^ m = d ^ m * w * w⁻¹ := by group
      _ = 1 := by rw [← this]; group
  have hd1 : d = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right k hm.coprime_two_right) (orderOf_dvd_of_pow_eq_one hdm)
    (orderOf_dvd_of_pow_eq_one hd))
  calc y * w * y⁻¹ = d * w := by rw [hdd]; group
    _ = w := by rw [hd1, one_mul]

omit [Finite G] in
theorem norm_decomp {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {w w₁ w₂ : G}
    (hw : w ∈ A) (hw₁ : w₁ ∈ A) (hw₂ : w₂ ∈ A) :
    w = (w₁ * w⁻¹ * (w₂ * w⁻¹))⁻¹ * (w * w₁ * w₂ * (w * w)⁻¹) := by
  symm
  calc (w₁ * w⁻¹ * (w₂ * w⁻¹))⁻¹ * (w * w₁ * w₂ * (w * w)⁻¹) =
        w * w₂⁻¹ * w * (w₁⁻¹ * w) * w₁ * w₂ * w⁻¹ * w⁻¹ := by group
    _ = w * w₂⁻¹ * w * (w * w₁⁻¹) * w₁ * w₂ * w⁻¹ * w⁻¹ := by rw [hA _ (A.inv_mem hw₁) _ hw]
    _ = w * (w₂⁻¹ * (w * w)) * w₂ * w⁻¹ * w⁻¹ := by group
    _ = w * ((w * w) * w₂⁻¹) * w₂ * w⁻¹ * w⁻¹ := by
        rw [hA _ (A.inv_mem hw₂) _ (A.mul_mem hw hw)]
    _ = w := by group

abbrev nK (T V : Subgroup G) (g : G) : Subgroup G :=
  centerOf (fsuU T V) ⊓ Subgroup.centralizer (kI T V g : Set G)

omit [Finite G] in
theorem conj_mem_nK {h n : G} (hh : h ∈ l32nH T V) (hn : n ∈ nK T V g) :
    h * n * h⁻¹ ∈ nK T V g :=
  ⟨CtxI.conj_mem_zU hh hn.1, (Subgroup.mem_normalizer_iff.mp
    (le_normalizer_centralizer (CtxI.le_normalizer_kI hh)) n).mp hn.2⟩

omit [Finite G] in
theorem le_normalizer_cHat : l32nH T V ≤ Subgroup.normalizer (l32nCHat T V : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨fun he => conj_mem_cHat hh he, fun he => ?_⟩
  have h1 := conj_mem_cHat ((l32nH T V).inv_mem hh) he
  have e1 : h⁻¹ * (h * e * h⁻¹) * h⁻¹⁻¹ = e := by group
  rwa [e1] at h1

namespace CtxI

variable (C : CtxI G T L V V₂ g D)
include C

theorem H_V1 {h v : G} (hh : h ∈ l32nH T V) (hv : v ∈ fsuV1 T V) : h * v * h⁻¹ = v := by
  have := Subgroup.mem_centralizer_iff.mp
    (le_centralizer_normalizer_of_card_eq_two C.ctx.card_V1 hv) h hh
  calc h * v * h⁻¹ = v * h * h⁻¹ := by rw [this]
    _ = v := by group

theorem V1_le_nK : fsuV1 T V ≤ nK T V g := fun v hv =>
  ⟨C.ctx.lt.le hv, Subgroup.mem_centralizer_iff.mpr fun k hk => by
    have := C.H_V1 (C.kI_le hk) hv
    calc k * v = k * v * k⁻¹ * k := by group
      _ = v * k := by rw [this]⟩

end CtxI

omit [Finite G] in
theorem rho_conj {h y : G} (hhN : h ∈ Subgroup.normalizer (fsuU T V : Set G))
    (hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G))
    (hN : h⁻¹ * y * h ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨h⁻¹ * y * h, hN⟩ = (D.ρ ⟨h, hhN⟩)⁻¹ * D.ρ ⟨y, hyN⟩ * D.ρ ⟨h, hhN⟩ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

namespace CtxI.TransData

variable {C : CtxI G T L V V₂ g D} {x c : G} (X : TransData C x c)
include X

theorem le_pCoreOf (h64 : G64.LemmaG64) :
    kI T V g ⊓ l32nCHat T V ≤ pCoreOf 2 (l32nH T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans C.kI_le)
    (fun h hh => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_kI hh, le_normalizer_cHat hh⟩) ?_
  rintro ⟨f, hfK, hfE⟩
  obtain ⟨a, m, hm2, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos f).ne' 2
    (by norm_num)
  have hmo : Odd m := by
    rcases Nat.even_or_odd m with h | h
    · exact absurd (even_iff_two_dvd.mp h) hm2
    · exact h
  set f' := f ^ (2 ^ a) with hf'
  have hf'K : f' ∈ kI T V g := (kI T V g).pow_mem hfK _
  have hf'E : f' ∈ l32nCHat T V := (l32nCHat T V).pow_mem hfE _
  have hf'm : f' ^ m = 1 := by rw [hf', ← pow_mul, ← hom, pow_orderOf_eq_one]
  have hf'P := X.cent_of_hat h64 hf'K hf'E
  have hf'Z : ∀ w ∈ centerOf (fsuU T V), f' * w * f'⁻¹ = w := by
    intro w hw
    have hd := X.comm_mem_vP hf'K hw
    refine conj_eq_of_odd (k := 1) hmo hf'm ?_ ?_
    · have := Subgroup.mem_centralizer_iff.mp hf'P _ hd
      calc f' * (f' * w * f'⁻¹ * w⁻¹) * f'⁻¹ = (f' * w * f'⁻¹ * w⁻¹) * f' * f'⁻¹ := by
            rw [this]
        _ = f' * w * f'⁻¹ * w⁻¹ := by group
    · rw [pow_one, pow_two]
      exact C.vH_sq (X.vP_le hd)
  have hf'U : ∀ u ∈ fsuU T V, f' * u * f'⁻¹ = u := by
    intro u hu
    have hd : f' * u * f'⁻¹ * u⁻¹ ∈ centerOf (fsuU T V) := hf'E.2.2 u hu
    obtain ⟨k, hk⟩ := C.ctx.U2 ⟨_, hd.1⟩
    exact conj_eq_of_odd (k := k) hmo hf'm (hf'Z _ hd) (by simpa using congrArg Subtype.val hk)
  have hf'Q : f' ∈ pCoreOf 2 (l32nH T V) := by
    rw [← C.ctx.q_tilde]
    refine ⟨C.kI_le hf'K, C.kI_le hf'K, fun u hu => ?_⟩
    rw [hf'U u hu, mul_inv_cancel]
    exact one_mem _
  obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l32nH T V) ⟨f', hf'Q⟩
  have hb' : f' ^ (2 ^ b) = 1 := by simpa using congrArg Subtype.val hb
  have hf'1 : f' = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right b hmo.coprime_two_right) (orderOf_dvd_of_pow_eq_one hf'm)
    (orderOf_dvd_of_pow_eq_one hb'))
  exact ⟨a, Subtype.ext (by rw [Subgroup.coe_pow]; exact hf'1)⟩

theorem cent_zU_of_cHat (h64 : G64.LemmaG64) {f : G} (hfK : f ∈ kI T V g)
    (hfE : f ∈ l32nCHat T V) {w : G} (hw : w ∈ centerOf (fsuU T V)) : f * w * f⁻¹ = w := by
  have hfQ := X.le_pCoreOf h64 ⟨hfK, hfE⟩
  rw [← C.ctx.q_tilde] at hfQ
  have h1 : f * w * f⁻¹ * w⁻¹ ∈ fsuV1 T V := hfQ.2.2 w hw.1
  have h3 : f * w * f⁻¹ * w⁻¹ = 1 :=
    X.eq_one_of_cent h64 (X.comm_mem_vP hfK hw) (fun k hk => C.H_V1 (C.kI_le hk) h1)
  calc f * w * f⁻¹ = f * w * f⁻¹ * w⁻¹ * w := by group
    _ = w := by rw [h3, one_mul]

theorem rho_x_sq (hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨x, hxN⟩ * D.ρ ⟨x, hxN⟩ = 1 := by
  have hm := L128A.HatU.rho_mem_img D X.x_mem hxN
  have h2 := pow_card_eq_one' (G := ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)))
    (x := ⟨_, hm⟩)
  rw [C.card_zd, pow_two] at h2
  exact congrArg Subtype.val h2

theorem good (h64 : G64.LemmaG64) {y : G} (hyK : y ∈ kI T V g)
    (hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G)) (hy3 : D.ρ ⟨y, hyN⟩ ^ 3 = 1)
    (hy1 : D.ρ ⟨y, hyN⟩ ≠ 1) :
    y ^ 3 ∈ kI T V g ⊓ l32nCHat T V ∧ y ^ 3 ∈ Subgroup.centralizer (vP T V c : Set G) ∧
      y ∉ Subgroup.centralizer (vP T V c : Set G) := by
  have hyH := C.kI_le hyK
  have hy3K : y ^ 3 ∈ kI T V g := (kI T V g).pow_mem hyK 3
  have hy3N : y ^ 3 ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    (Subgroup.normalizer _).pow_mem hyN 3
  have e1 : (⟨y ^ 3, hy3N⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨y, hyN⟩ ^ 3 := rfl
  have hρ : D.ρ ⟨y ^ 3, hy3N⟩ = 1 := by rw [e1, map_pow, hy3]
  have hy3E := (L14332.rho_eq_one_iff_mem (C.kI_le hy3K) hy3N).mp hρ
  exact ⟨⟨hy3K, hy3E⟩, X.cent_of_hat h64 hy3K hy3E, fun hyc => hy1
    ((L14332.rho_eq_one_iff_mem hyH hyN).mpr
      (C.mem_cHat_of_mem_centralizer hyK (X.cent_vH hyK hyc)))⟩

theorem cent_cy (h64 : G64.LemmaG64) {y : G} (hyK : y ∈ kI T V g)
    (hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G)) (hy3 : D.ρ ⟨y, hyN⟩ ^ 3 = 1)
    (hy1 : D.ρ ⟨y, hyN⟩ ≠ 1) {n : G} (hn : n ∈ centerOf (fsuU T V))
    (hny : y * n * y⁻¹ = n) : x * n * x⁻¹ = n := by
  obtain ⟨e⟩ := C.iso
  have hyH := C.kI_le hyK
  have hxK := zUg_le_kI X.x_mem
  have hxN := L14332.l32nH_le_normalizer_fsuU T V X.x_H
  set f := x * y * x⁻¹ * y with hf
  have hfK : f ∈ kI T V g :=
    (kI T V g).mul_mem ((kI T V g).mul_mem ((kI T V g).mul_mem hxK hyK) ((kI T V g).inv_mem hxK))
      hyK
  have hfE : f ∈ l32nCHat T V := by
    have hfN := L14332.l32nH_le_normalizer_fsuU T V (C.kI_le hfK)
    refine (L14332.rho_eq_one_iff_mem (D := D) (C.kI_le hfK) hfN).mp ?_
    have e1 : (⟨f, hfN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
        ⟨x, hxN⟩ * ⟨y, hyN⟩ * ⟨x, hxN⟩⁻¹ * ⟨y, hyN⟩ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv]
    set σ := e ⟨_, L128A.HatU.rho_mem_img D hyK hyN⟩ with hσ
    set τ := e ⟨_, L128A.HatU.rho_mem_img D hxK hxN⟩ with hτ
    have hσ3 : σ ^ 3 = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨_, L128A.HatU.rho_mem_img D hyK hyN⟩ : ↥(D.img (kI T V g))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hy3)
      rw [this, map_one]
    have hτ2 : τ * τ = 1 := by
      rw [hτ, ← map_mul]
      have : (⟨_, L128A.HatU.rho_mem_img D hxK hxN⟩ : ↥(D.img (kI T V g))) *
          ⟨_, L128A.HatU.rho_mem_img D hxK hxN⟩ = 1 := Subtype.ext (X.rho_x_sq hxN)
      rw [this, map_one]
    have hτ1 : τ ≠ 1 := by
      rw [hτ, Ne, MulEquiv.map_eq_one_iff]
      exact fun h => X.x_ne hxN (congrArg Subtype.val h)
    have hinv := s3_inv σ τ hσ3 hτ2 hτ1
    have h1 : e (⟨_, L128A.HatU.rho_mem_img D hxK hxN⟩ * ⟨_, L128A.HatU.rho_mem_img D hyK hyN⟩ *
        (⟨_, L128A.HatU.rho_mem_img D hxK hxN⟩)⁻¹ * ⟨_, L128A.HatU.rho_mem_img D hyK hyN⟩) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, ← hσ, ← hτ, hinv, inv_mul_cancel]
    rw [MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  have hm : x * n * x⁻¹ ∈ centerOf (fsuU T V) := CtxI.conj_mem_zU X.x_H hn
  have hp : y⁻¹ * (x * n * x⁻¹) * y ∈ centerOf (fsuU T V) := by
    simpa using CtxI.conj_mem_zU ((l32nH T V).inv_mem hyH) hm
  have h1 := X.cent_zU_of_cHat h64 hfK hfE hp
  have h2 : f * (y⁻¹ * (x * n * x⁻¹) * y) * f⁻¹ = x * n * x⁻¹ := by
    rw [hf]
    calc x * y * x⁻¹ * y * (y⁻¹ * (x * n * x⁻¹) * y) * (x * y * x⁻¹ * y)⁻¹ =
          x * (y * n * y⁻¹) * x⁻¹ := by group
      _ = x * n * x⁻¹ := by rw [hny]
  have h3 : y⁻¹ * (x * n * x⁻¹) * y = x * n * x⁻¹ := h1.symm.trans h2
  have hym : y * (x * n * x⁻¹) * y⁻¹ = x * n * x⁻¹ := by
    calc y * (x * n * x⁻¹) * y⁻¹ = y * (y⁻¹ * (x * n * x⁻¹) * y) * y⁻¹ := by rw [h3]
      _ = x * n * x⁻¹ := by group
  rcases X.comm n hn with h | h
  · calc x * n * x⁻¹ = x * n * x⁻¹ * n⁻¹ * n := by group
      _ = n := by rw [h, one_mul]
  · exfalso
    have hyc : y * c * y⁻¹ = c := by
      rw [← h]
      calc y * (x * n * x⁻¹ * n⁻¹) * y⁻¹ = (y * (x * n * x⁻¹) * y⁻¹) * (y * n * y⁻¹)⁻¹ := by
            group
        _ = x * n * x⁻¹ * n⁻¹ := by rw [hym, hny]
    obtain ⟨-, hy3c, hy1c⟩ := X.good h64 hyK hyN hy3 hy1
    exact X.c_ne (X.eq_one_of_fix h64 (H_le_normalizer_vP c hyH) hy3c hy1c (c_mem_vP c) hyc)

theorem mem_nK (h64 : G64.LemmaG64) {y : G} (hyK : y ∈ kI T V g)
    (hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G)) (hy3 : D.ρ ⟨y, hyN⟩ ^ 3 = 1)
    (hy1 : D.ρ ⟨y, hyN⟩ ≠ 1) {n : G} (hn : n ∈ centerOf (fsuU T V))
    (hny : y * n * y⁻¹ = n) : n ∈ nK T V g := by
  refine Subgroup.mem_inf.mpr ⟨hn, ?_⟩
  have hxh : ∀ h ∈ l32nH T V, (h * x * h⁻¹) * n * (h * x * h⁻¹)⁻¹ = n := by
    intro h hh
    have hhN := L14332.l32nH_le_normalizer_fsuU T V hh
    have hn' : h⁻¹ * n * h ∈ centerOf (fsuU T V) := by
      simpa using CtxI.conj_mem_zU ((l32nH T V).inv_mem hh) hn
    have hy'K : h⁻¹ * y * h ∈ kI T V g := by
      simpa using (Subgroup.mem_normalizer_iff.mp (le_normalizer_kI ((l32nH T V).inv_mem hh))
        y).mp hyK
    have hy'N := L14332.l32nH_le_normalizer_fsuU T V (C.kI_le hy'K)
    have hρ := rho_conj (D := D) hhN hyN hy'N
    have hy'3 : D.ρ ⟨h⁻¹ * y * h, hy'N⟩ ^ 3 = 1 := by
      have hc := conj_pow (a := (D.ρ ⟨h, hhN⟩)⁻¹) (b := D.ρ ⟨y, hyN⟩) (i := 3)
      rw [inv_inv] at hc
      rw [hρ, hc, hy3]
      group
    have hy'1 : D.ρ ⟨h⁻¹ * y * h, hy'N⟩ ≠ 1 := by
      rw [hρ]
      intro h1
      apply hy1
      calc D.ρ ⟨y, hyN⟩ = D.ρ ⟨h, hhN⟩ * ((D.ρ ⟨h, hhN⟩)⁻¹ * D.ρ ⟨y, hyN⟩ * D.ρ ⟨h, hhN⟩) *
            (D.ρ ⟨h, hhN⟩)⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hy'n : (h⁻¹ * y * h) * (h⁻¹ * n * h) * (h⁻¹ * y * h)⁻¹ = h⁻¹ * n * h := by
      calc (h⁻¹ * y * h) * (h⁻¹ * n * h) * (h⁻¹ * y * h)⁻¹ = h⁻¹ * (y * n * y⁻¹) * h := by group
        _ = h⁻¹ * n * h := by rw [hny]
    have := X.cent_cy h64 hy'K hy'N hy'3 hy'1 hn' hy'n
    calc (h * x * h⁻¹) * n * (h * x * h⁻¹)⁻¹ = h * (x * (h⁻¹ * n * h) * x⁻¹) * h⁻¹ := by group
      _ = h * (h⁻¹ * n * h) * h⁻¹ := by rw [this]
      _ = n := by group
  have hK : kI T V g ≤ Subgroup.centralizer ({n} : Set G) := conjClosure_le fun h hh z hz => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hn' : h⁻¹ * n * h ∈ centerOf (fsuU T V) := by
      simpa using CtxI.conj_mem_zU ((l32nH T V).inv_mem hh) hn
    have hzfix : z * (h⁻¹ * n * h) * z⁻¹ = h⁻¹ * n * h := by
      rcases X.zg_cases hz with h1 | h1
      · exact h1 _ hn'
      · rw [h1 _ hn']
        calc x * (h⁻¹ * n * h) * x⁻¹ = h⁻¹ * ((h * x * h⁻¹) * n * (h * x * h⁻¹)⁻¹) * h := by
              group
          _ = h⁻¹ * n * h := by rw [hxh h hh]
    calc h * z * h⁻¹ * n = h * (z * (h⁻¹ * n * h) * z⁻¹) * z * h⁻¹ := by group
      _ = h * (h⁻¹ * n * h) * z * h⁻¹ := by rw [hzfix]
      _ = n * (h * z * h⁻¹) := by group
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (hK hk)

theorem exists_decomp (h64 : G64.LemmaG64) {w : G} (hw : w ∈ centerOf (fsuU T V)) :
    ∃ v ∈ vP T V c, ∃ n ∈ nK T V g, w = v * n := by
  obtain ⟨y, hyK, -, -, hyN, hy3, hy1⟩ := C.exists_three
  have hyH := C.kI_le hyK
  obtain ⟨hy3KE, -, -⟩ := X.good h64 hyK hyN hy3 hy1
  have hy3Z : ∀ z ∈ centerOf (fsuU T V), y ^ 3 * z * (y ^ 3)⁻¹ = z := fun z hz =>
    X.cent_zU_of_cHat h64 hy3KE.1 hy3KE.2 hz
  have hyyH : y * y ∈ l32nH T V := (l32nH T V).mul_mem hyH hyH
  set w₁ := y * w * y⁻¹ with hw₁d
  set w₂ := y * y * w * (y * y)⁻¹ with hw₂d
  have hw₁ : w₁ ∈ centerOf (fsuU T V) := CtxI.conj_mem_zU hyH hw
  have hw₂ : w₂ ∈ centerOf (fsuU T V) := CtxI.conj_mem_zU hyyH hw
  have hA : ∀ a ∈ centerOf (fsuU T V), ∀ b ∈ centerOf (fsuU T V), a * b = b * a :=
    fun a ha b hb => zU_comm ha hb
  refine ⟨(w₁ * w⁻¹ * (w₂ * w⁻¹))⁻¹, ?_, w * w₁ * w₂ * (w * w)⁻¹, ?_,
    norm_decomp hA hw hw₁ hw₂⟩
  · exact (vP T V c).inv_mem ((vP T V c).mul_mem (X.comm_mem_vP hyK hw)
      (X.comm_mem_vP ((kI T V g).mul_mem hyK hyK) hw))
  · have hww : w * w ∈ fsuV1 T V := C.sq w hw.1
    have hn₀ : w * w₁ * w₂ ∈ centerOf (fsuU T V) :=
      (centerOf _).mul_mem ((centerOf _).mul_mem hw hw₁) hw₂
    refine X.mem_nK h64 hyK hyN hy3 hy1 ((centerOf _).mul_mem hn₀
      ((centerOf _).inv_mem (C.ctx.lt.le hww))) ?_
    have e1 : y * (w * w₁ * w₂) * y⁻¹ = w₁ * w₂ * (y ^ 3 * w * (y ^ 3)⁻¹) := by
      rw [hw₁d, hw₂d]
      group
    have hyn₀ : y * (w * w₁ * w₂) * y⁻¹ = w * w₁ * w₂ := by
      rw [e1, hy3Z w hw, hA _ ((centerOf _).mul_mem hw₁ hw₂) _ hw, ← mul_assoc]
    have hyww : y * (w * w)⁻¹ * y⁻¹ = (w * w)⁻¹ := by
      have := C.H_V1 hyH hww
      calc y * (w * w)⁻¹ * y⁻¹ = (y * (w * w) * y⁻¹)⁻¹ := by group
        _ = (w * w)⁻¹ := by rw [this]
    calc y * (w * w₁ * w₂ * (w * w)⁻¹) * y⁻¹ =
          (y * (w * w₁ * w₂) * y⁻¹) * (y * (w * w)⁻¹ * y⁻¹) := by group
      _ = w * w₁ * w₂ * (w * w)⁻¹ := by rw [hyn₀, hyww]

end CtxI.TransData

end L14325

end CFSG.Quasithin.H13
