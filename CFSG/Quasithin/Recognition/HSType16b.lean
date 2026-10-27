module

public import CFSG.Quasithin.Recognition.HSType16a
public import CFSG.Quasithin.Recognition.HSTypeFactAut
public import CFSG.Quasithin.Recognition.HSType15c
public import CFSG.Quasithin.Recognition.HSType15e

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.L34Amalgam MulAction
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

namespace S6Model

variable (M : S6Model z s)

theorem conj_mem_L1 {n : ↥(hsNB z s)} (hn : NormLamS (M.π n)) {k : G} (hk : k ∈ M.L1) :
    (n : G) * k * (n : G)⁻¹ ∈ M.L1 := by
  obtain ⟨hkN, hkπ⟩ := M.mem_pre.mp hk
  have hm : (n : G) * k * (n : G)⁻¹ ∈ hsNB z s :=
    (hsNB z s).mul_mem ((hsNB z s).mul_mem n.2 hkN) ((hsNB z s).inv_mem n.2)
  refine M.mem_pre.mpr ⟨hm, ?_⟩
  have e : (⟨(n : G) * k * (n : G)⁻¹, hm⟩ : ↥(hsNB z s)) = n * ⟨k, hkN⟩ * n⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  exact normLamS_iff.mp hn _ hkπ

include M in
theorem exists_i [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x : ↥(hsNB z s)}
    (hx3 : orderOf (x : G) = 3) (hπx : M.π x = σS0) :
    ∃ i : ↥(hsNB z s), (i : G) * i = 1 ∧ (i : G) * x * (i : G)⁻¹ = (x : G)⁻¹ ∧
      M.π i ∈ stabS ∧ M.π i ∉ lamS ∧ M.π i ∉ fixS ∧ NormLamS (M.π i) ∧
        ∃ c : G, c * z * c⁻¹ = i := by
  obtain ⟨v, hvx, σ, hσ, hπv⟩ := M.exists_normalizing_lift h hsmemH hsnotK hss hg₀ x hx3 ιS
    (by rw [hπx]; exact ιS_conj)
  rw [hπx] at hσ
  obtain ⟨hst, hl, hfx, hfpf, hv2, hvinv, hnorm⟩ := ιS_facts σ (mem_zpowers_σS0 hσ)
  rw [← hπv] at hst hl hfx hfpf hv2 hvinv hnorm
  have hvx' : (v : G) * x * (v : G)⁻¹ = (x : G)⁻¹ := by
    rcases eq_of_mem_zpowers_three hx3 hvx with h1 | h1 | h1
    · exfalso
      have : (x : G) = 1 := by
        calc (x : G) = (v : G)⁻¹ * ((v : G) * x * (v : G)⁻¹) * v := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at hx3
      exact absurd hx3 (by decide)
    · exfalso
      have e : v * x * v⁻¹ = x := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact h1)
      have e' := congrArg M.π e
      rw [map_mul, map_mul, map_inv, hπx, hvinv] at e'
      exact σS0_inv_ne e'
    · exact h1
  have hv2' : (v : G) * v = 1 := by
    have hB : ((v * v : ↥(hsNB z s)) : G) ∈ hsB z s := (M.ker _).mp (by rw [map_mul, hv2])
    refine M.eq_one_of_mem_hsB_comm hπx hB ?_
    calc (v : G) * v * x = v * (v * x * (v : G)⁻¹) * (v : G)⁻¹ * (v * v) := by group
      _ = v * (x : G)⁻¹ * (v : G)⁻¹ * (v * v) := by rw [hvx']
      _ = ((v : G) * x * (v : G)⁻¹)⁻¹ * (v * v) := by group
      _ = x * (v * v) := by rw [hvx', inv_inv]
  obtain ⟨c, hc⟩ := M.conj_z_of_fpf h hsmemH hsnotK hss hv2' hfpf
  exact ⟨v, hv2', hvx', hst, hl, hfx, hnorm, c, hc⟩

include M in
theorem exists_adjust [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {g : G}
    (hg : g ∈ Subgroup.normalizer (M.V2 : Set G)) (hgNN : g ∉ M.NN) {x : G} (hxRX : x ∈ M.RX)
    (hx3 : orderOf x = 3) :
    ∃ g' ∈ Subgroup.normalizer (M.V2 : Set G), g' ∉ M.NN ∧
      M.L1.map (MulAut.conj g').toMonoidHom = M.L1.map (MulAut.conj g).toMonoidHom ∧
      ∃ hx' : g'⁻¹ * x * g' ∈ hsNB z s, M.π ⟨g'⁻¹ * x * g', hx'⟩ = σS0 := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (M.V2 : Set G) := (Subgroup.normalizer _).inv_mem hg
  have hyNN : g⁻¹ * x * g ∈ M.NN := by
    have := M.conj_mem_NN h hsmemH hsnotK hss hg₀ hg' (M.pre_mono inf_le_right hxRX)
    rwa [inv_inv] at this
  obtain ⟨hyN, hyπ⟩ := M.mem_pre.mp hyNN
  have hy3 : (g⁻¹ * x * g) ^ 3 = 1 := by
    rw [show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, ← map_pow, ← hx3, pow_orderOf_eq_one,
      map_one]
  have hτ3 : M.π ⟨g⁻¹ * x * g, hyN⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨g⁻¹ * x * g, hyN⟩ : ↥(hsNB z s)) ^ 3 = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hy3), map_one]
  have hτ1 : M.π ⟨g⁻¹ * x * g, hyN⟩ ≠ 1 := by
    intro h1
    have hB : g⁻¹ * x * g ∈ hsB z s := (M.ker _).mp h1
    have e := M.mul_self_of_mem_hsB hB
    have key : ∀ y : G, y = y ^ 3 * (y * y)⁻¹ := fun y => by group
    have hy1 : g⁻¹ * x * g = 1 := by
      rw [key (g⁻¹ * x * g), hy3, e]
      group
    have hx1 : x = 1 := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [hy1]; group
    rw [hx1, orderOf_one] at hx3
    exact absurd hx3 (by decide)
  obtain ⟨ℓ, hℓ, hℓτ⟩ := exists_ell _ hyπ hτ3 hτ1
  obtain ⟨hℓs, hℓn, hℓn'⟩ := ellList_facts ℓ hℓ
  obtain ⟨n, hn⟩ := M.π_surj ℓ
  have hnNN : (n : G) ∈ M.NN := M.mem_pre.mpr ⟨n.2, by
    rw [show (⟨(n : G), n.2⟩ : ↥(hsNB z s)) = n from rfl, hn]
    exact hℓs⟩
  refine ⟨g * (n : G)⁻¹, (Subgroup.normalizer _).mul_mem hg
    ((Subgroup.normalizer _).inv_mem (M.NN_le_normalizer hnNN)), fun hm => hgNN ?_, ?_, ?_⟩
  · have := M.NN.mul_mem hm hnNN
    rwa [inv_mul_cancel_right] at this
  · ext k
    rw [mem_map_conj_iff, mem_map_conj_iff,
      show (g * (n : G)⁻¹)⁻¹ * k * (g * (n : G)⁻¹) = (n : G) * (g⁻¹ * k * g) * (n : G)⁻¹ by
        group]
    constructor
    · intro hk'
      have := M.conj_mem_L1 (n := n⁻¹) (by rw [map_inv, hn]; exact hℓn') hk'
      rwa [show ((n⁻¹ : ↥(hsNB z s)) : G) * ((n : G) * (g⁻¹ * k * g) * (n : G)⁻¹) *
          ((n⁻¹ : ↥(hsNB z s)) : G)⁻¹ = g⁻¹ * k * g by
        rw [Subgroup.coe_inv]; group] at this
    · intro hk'
      exact M.conj_mem_L1 (by rw [hn]; exact hℓn) hk'
  · have hx'N : (g * (n : G)⁻¹)⁻¹ * x * (g * (n : G)⁻¹) ∈ hsNB z s := by
      rw [show (g * (n : G)⁻¹)⁻¹ * x * (g * (n : G)⁻¹) = (n : G) * (g⁻¹ * x * g) * (n : G)⁻¹ by
        group]
      exact (hsNB z s).mul_mem ((hsNB z s).mul_mem n.2 hyN) ((hsNB z s).inv_mem n.2)
    refine ⟨hx'N, ?_⟩
    have e : (⟨(g * (n : G)⁻¹)⁻¹ * x * (g * (n : G)⁻¹), hx'N⟩ : ↥(hsNB z s)) =
        n * ⟨g⁻¹ * x * g, hyN⟩ * n⁻¹ := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group)
    rw [e, map_mul, map_mul, map_inv, hn, hℓτ]

@[expose] noncomputable def conjOn {L : Subgroup G} {i : G}
    (hiL : i ∈ Subgroup.normalizer (L : Set G)) : ↥L ≃* ↥L :=
  ((MulAut.conj i).subgroupMap L).trans (MulEquiv.subgroupCongr (by
    ext y
    change y ∈ L.map (MulAut.conj i).toMonoidHom ↔ y ∈ L
    rw [mem_map_conj_iff]
    have := Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hiL) y
    rw [inv_inv] at this
    exact this.symm))

theorem conjOn_apply {L : Subgroup G} {i : G} (hiL : i ∈ Subgroup.normalizer (L : Set G))
    (y : ↥L) : ((conjOn hiL y : ↥L) : G) = i * y * i⁻¹ := rfl

include M in
theorem not_mem_normalizer_L [Finite G] (hfact : FactAutL34) (h : HSSetting z V)
    (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G}
    (hg₀ : g₀ * z * g₀⁻¹ = s) {L : Subgroup G} (hL1 : M.L1 ≤ L)
    (Φ : ↥L ≃* ↥(stabilizer M22 (0 : Fin 22)))
    (hΦ : ∀ x : ↥L, (x : G) ∈ M.L1 ↔
      ((Φ x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab)
    {i : ↥(hsNB z s)} (hi2 : (i : G) * i = 1) (hil : M.π i ∉ lamS) (hin : NormLamS (M.π i))
    {c : G} (hc : c * z * c⁻¹ = i) : (i : G) ∉ Subgroup.normalizer (L : Set G) := by
  intro hiNL
  have hii : (i : G)⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
  have hiL1 : ∀ k : G, k ∈ M.L1 ↔ (i : G) * k * (i : G)⁻¹ ∈ M.L1 := by
    intro k
    refine ⟨fun hk => M.conj_mem_L1 hin hk, fun hk => ?_⟩
    have := M.conj_mem_L1 hin hk
    rwa [show (i : G) * ((i : G) * k * (i : G)⁻¹) * (i : G)⁻¹ = ((i : G) * i) * k *
      ((i : G) * i)⁻¹ by group, hi2, one_mul, inv_one, mul_one] at this
  set β₀ := conjOn hiNL with hβ₀
  let β : ↥(stabilizer M22 (0 : Fin 22)) ≃* ↥(stabilizer M22 (0 : Fin 22)) :=
    (Φ.symm.trans β₀).trans Φ
  have hβ : ∀ w, β w = Φ (β₀ (Φ.symm w)) := fun w => rfl
  have hβ₀β₀ : ∀ y : ↥L, β₀ (β₀ y) = y := by
    intro y
    apply Subtype.ext
    rw [conjOn_apply, conjOn_apply]
    calc (i : G) * ((i : G) * y * (i : G)⁻¹) * (i : G)⁻¹ = ((i : G) * i) * y *
        ((i : G) * i)⁻¹ := by group
      _ = y := by rw [hi2, one_mul, inv_one, mul_one]
  have h2 : ∀ w, β (β w) = w := by
    intro w
    rw [hβ, hβ, MulEquiv.symm_apply_apply, hβ₀β₀, MulEquiv.apply_symm_apply]
  have hnorm : ∀ w : ↥(stabilizer M22 (0 : Fin 22)), (w : M22) ∈ m22TwoStab ↔
      ((β w : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab := by
    intro w
    obtain ⟨x, rfl⟩ := Φ.surjective w
    rw [hβ, MulEquiv.symm_apply_apply, ← hΦ, ← hΦ, conjOn_apply]
    exact hiL1 _
  rcases hfact β h2 hnorm with ⟨d, hd, hβd⟩ | ⟨w, hw7, hβw⟩
  ·
    set d' := Φ.symm d with hd'
    have hd'L1 : (d' : G) ∈ M.L1 := by
      rw [hΦ, hd', MulEquiv.apply_symm_apply]
      exact hd
    have hconj : ∀ y : ↥L, (i : G) * y * (i : G)⁻¹ = d' * y * (d' : G)⁻¹ := by
      intro y
      have e := hβd (Φ y)
      rw [hβ, MulEquiv.symm_apply_apply] at e
      have e' := congrArg (fun u => ((Φ.symm u : ↥L) : G)) e
      simp only [MulEquiv.symm_apply_apply, map_mul, map_inv] at e'
      rw [← conjOn_apply hiNL]
      rw [e']
      simp [hd']
    set e := (d' : G)⁻¹ * i with he
    have heC : ∀ y ∈ L, e * y = y * e := by
      intro y hy
      have h1 := hconj ⟨y, hy⟩
      simp only at h1
      calc e * y = (d' : G)⁻¹ * ((i : G) * y * (i : G)⁻¹) * i := by rw [he]; group
        _ = (d' : G)⁻¹ * (d' * y * (d' : G)⁻¹) * i := by rw [h1]
        _ = y * e := by rw [he]; group
    have heB : e ∈ hsB z s := by
      rw [← h.centralizer_hsB hsmemH hsnotK hss hg₀]
      exact Subgroup.mem_centralizer_iff.mpr fun b hb => (heC b (hL1 (M.hsB_le_L1 hb))).symm
    obtain ⟨u, hu⟩ := M.surj e heB
    obtain ⟨y₀, hy₀⟩ := M.π_surj βS
    have hy₀L : (y₀ : G) ∈ L := hL1 (M.mem_pre.mpr ⟨y₀.2, by
      rw [show (⟨(y₀ : G), y₀.2⟩ : ↥(hsNB z s)) = y₀ from rfl, hy₀]
      exact βS_mem⟩)
    have h3 := M.act y₀ u
    have h4 : (y₀ : G) * e * (y₀ : G)⁻¹ = e := by
      rw [← heC _ hy₀L]
      group
    rw [hy₀, hu, h4, ← hu] at h3
    have hu0 : u = 0 := eq_zero_of_actS6_βS u (M.inj h3).symm
    have he1 : e = 1 := by rw [← hu, hu0, M.Φ_zero]
    have hid : (i : G) = d' := by
      calc (i : G) = (d' : G) * e := by rw [he]; group
        _ = d' := by rw [he1, mul_one]
    exact hil (M.π_mem_of_mem_pre (show (i : G) ∈ M.L1 by rw [hid]; exact hd'L1) i.2)
  ·
    set y := Φ.symm w with hy
    have hyfix : (i : G) * y * (i : G)⁻¹ = y := by
      have e := congrArg Φ.symm hβw
      rw [hβ, MulEquiv.symm_apply_apply] at e
      rw [← conjOn_apply hiNL, e]
    have hy7 : orderOf (y : G) = 7 := by
      rw [Subgroup.orderOf_coe, hy, MulEquiv.orderOf_eq, hw7]
    have hyC : (y : G) ∈ Subgroup.centralizer ({(i : G)} : Set G) := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc (y : G) * i = (i : G) * y * (i : G)⁻¹ * i := by rw [hyfix]
        _ = i * y := by group
    have hcard : Nat.card ↥(Subgroup.centralizer ({(i : G)} : Set G)) = 64 * 120 := by
      have h1 := centralizer_map_mulEquiv (MulAut.conj c) z
      simp only [MulAut.conj_apply] at h1
      rw [← hc, h1, Subgroup.card_map_of_injective (MulAut.conj c).injective, h.card_H]
    have hdvd := orderOf_dvd_natCard (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({(i : G)} : Set G)))
    rw [Subgroup.orderOf_mk, hy7, hcard] at hdvd
    exact absurd hdvd (by decide)

include M in
theorem mem_alt_conj [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {g : G}
    (hg : g ∈ Subgroup.normalizer (M.V2 : Set G)) {i : ↥(hsNB z s)} (hi2 : (i : G) * i = 1)
    (hst : M.π i ∈ stabS) (hil : M.π i ∉ lamS) (hfx : M.π i ∉ fixS) (hin : NormLamS (M.π i))
    (hiL : (i : G) ∉ Subgroup.normalizer
      ((M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    ∃ hy : g⁻¹ * i * g ∈ hsNB z s, M.π ⟨g⁻¹ * i * g, hy⟩ ∈ stabS ∧
      M.π ⟨g⁻¹ * i * g, hy⟩ ∈ alternatingGroup (Fin 6) ∧ M.π ⟨g⁻¹ * i * g, hy⟩ ∉ lamS := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (M.V2 : Set G) := (Subgroup.normalizer _).inv_mem hg
  have hiNN : (i : G) ∈ M.NN := M.mem_pre.mpr ⟨i.2, hst⟩
  have hyNN : g⁻¹ * i * g ∈ M.NN := by
    have := M.conj_mem_NN h hsmemH hsnotK hss hg₀ hg' hiNN
    rwa [inv_inv] at this
  obtain ⟨hyN, hyπ⟩ := M.mem_pre.mp hyNN
  set y : ↥(hsNB z s) := ⟨g⁻¹ * i * g, hyN⟩ with hydef
  have hyy : (y : G) * y = 1 := by
    show g⁻¹ * i * g * (g⁻¹ * i * g) = 1
    rw [show g⁻¹ * i * g * (g⁻¹ * i * g) = g⁻¹ * ((i : G) * i) * g by group, hi2]
    group
  have hρρ : M.π y * M.π y = 1 := by
    rw [← map_mul, show y * y = 1 from Subtype.ext hyy, map_one]
  have h0 : M.π y ∉ lam0 := by
    intro hm
    have hyRX : g⁻¹ * i * g ∈ M.RX := M.mem_pre.mpr ⟨hyN, hm⟩
    have := M.conj_mem_RX h hsmemH hsnotK hss hg₀ hg hyRX
    rw [show g * (g⁻¹ * i * g) * g⁻¹ = (i : G) by group] at this
    exact hil (M.π_mem_of_mem_pre this i.2).1
  have h1 : ¬ NormLamS (M.π y) := by
    intro hn
    apply hiL
    have hL₂ : ∀ k ∈ M.L1.map (MulAut.conj g).toMonoidHom,
        (i : G) * k * (i : G)⁻¹ ∈ M.L1.map (MulAut.conj g).toMonoidHom := by
      intro k hk
      rw [mem_map_conj_iff] at hk ⊢
      have := M.conj_mem_L1 hn hk
      rwa [show (y : G) * (g⁻¹ * k * g) * (y : G)⁻¹ = g⁻¹ * ((i : G) * k * (i : G)⁻¹) * g by
        rw [hydef]; group] at this
    have hle : M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom ≤
        (M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom).comap (MulAut.conj (i : G)).toMonoidHom := by
      refine sup_le (fun k hk => ?_) (fun k hk => ?_)
      · exact Subgroup.mem_sup_left (M.conj_mem_L1 hin hk)
      · exact Subgroup.mem_sup_right (hL₂ k hk)
    exact Subgroup.mem_normalizer_fintype fun k hk => hle hk
  have h3 : M.π y ^ 3 ∉ fixS := by
    rw [pow_three, ← mul_assoc, hρρ, one_mul]
    intro hm
    have hyC := M.centralizes_of_mem_pre_fixS (M.mem_pre.mpr ⟨hyN, hm⟩)
    have hiC : (i : G) ∈ Subgroup.centralizer (M.V2 : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      have hv' : g⁻¹ * v * g ∈ M.V2 := M.conj_inv_mem_V2 hg hv
      have e := Subgroup.mem_centralizer_iff.mp hyC _ hv'
      calc v * i = g * ((g⁻¹ * v * g) * (g⁻¹ * i * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * i * g) * (g⁻¹ * v * g)) * g⁻¹ := by rw [e]
        _ = i * v := by group
    exact hfx (M.π_mem_of_mem_pre (M.mem_pre_fixS_of_centralizes i.2 hiC) i.2)
  have halt := mem_alt_of_stabS hyπ h0 h1 h3
  exact ⟨hyN, hyπ, halt, fun hm => h0 ⟨hm, hyπ⟩⟩

include M in
theorem exists_j_of_i [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {g : G}
    (hg : g ∈ Subgroup.normalizer (M.V2 : Set G)) (hgNN : g ∉ M.NN) {x : G}
    (hx3 : orderOf x = 3) (hx'N : g⁻¹ * x * g ∈ hsNB z s)
    (hπx' : M.π ⟨g⁻¹ * x * g, hx'N⟩ = σS0) {i : G} (hi2 : i * i = 1)
    (hix : i * x * i⁻¹ = x⁻¹) (hyN : g⁻¹ * i * g ∈ hsNB z s)
    (hyst : M.π ⟨g⁻¹ * i * g, hyN⟩ ∈ stabS)
    (hyalt : M.π ⟨g⁻¹ * i * g, hyN⟩ ∈ alternatingGroup (Fin 6)) :
    ∃ j : G, j ∈ M.L1.map (MulAut.conj g).toMonoidHom ∧ j ∉ M.L1 ∧ j * j = 1 ∧
      (i * j) ^ 3 = 1 := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (M.V2 : Set G) := (Subgroup.normalizer _).inv_mem hg
  set x' : ↥(hsNB z s) := ⟨g⁻¹ * x * g, hx'N⟩ with hx'
  have hx'3 : orderOf (x' : G) = 3 := by
    show orderOf (g⁻¹ * x * g) = 3
    rw [show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, MulEquiv.orderOf_eq, hx3]
  obtain ⟨t, htt, htx, htl, htl0, -⟩ := M.exists_t1 h hsmemH hsnotK hss hg₀ hx'3 hπx'
  obtain ⟨-, -, -, -, -, -, -, hinf, -⟩ := M.parabolics_of_g h hsmemH hsnotK hss hg₀ hg hgNN
  have htL1 : (t : G) ∈ M.L1 := M.mem_pre.mpr ⟨t.2, htl⟩
  have htRX : (t : G) ∉ M.RX := fun hm => htl0 (M.π_mem_of_mem_pre hm t.2)
  have hjt : g⁻¹ * (g * t * g⁻¹) * g = (t : G) := by group
  refine ⟨g * t * g⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [mem_map_conj_iff, hjt]
    exact htL1
  · intro hm
    have hjRX : g * t * g⁻¹ ∈ M.RX := by
      rw [← hinf]
      exact ⟨hm, mem_map_conj_iff.mpr (by rw [hjt]; exact htL1)⟩
    have := M.conj_mem_RX h hsmemH hsnotK hss hg₀ hg' hjRX
    rw [inv_inv, hjt] at this
    exact htRX this
  · rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * ((t : G) * t) * g⁻¹ by group, htt]
    group
  · set y : ↥(hsNB z s) := ⟨g⁻¹ * i * g, hyN⟩ with hy
    have hyy : (y : G) * y = 1 := by
      show g⁻¹ * i * g * (g⁻¹ * i * g) = 1
      rw [show g⁻¹ * i * g * (g⁻¹ * i * g) = g⁻¹ * (i * i) * g by group, hi2]
      group
    have hyx' : (y : G) * x' * (y : G)⁻¹ = (x' : G)⁻¹ := by
      show g⁻¹ * i * g * (g⁻¹ * x * g) * (g⁻¹ * i * g)⁻¹ = (g⁻¹ * x * g)⁻¹
      calc g⁻¹ * i * g * (g⁻¹ * x * g) * (g⁻¹ * i * g)⁻¹ = g⁻¹ * (i * x * i⁻¹) * g := by group
        _ = (g⁻¹ * x * g)⁻¹ := by rw [hix]; group
    have hπinv : ∀ u : ↥(hsNB z s), (u : G) * x' * (u : G)⁻¹ = (x' : G)⁻¹ →
        M.π u * σS0 * (M.π u)⁻¹ = σS0⁻¹ := by
      intro u hu
      have e : u * x' * u⁻¹ = x'⁻¹ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
        exact hu)
      have e' := congrArg M.π e
      rw [map_mul, map_mul, map_inv, map_inv, hπx'] at e'
      exact e'
    have hρ : M.π y ∈ evenInv := mem_evenInv hyst hyalt
      (by rw [← map_mul, show y * y = 1 from Subtype.ext hyy, map_one]) (hπinv y hyx')
    have hψ : M.π t ∈ jInv := mem_jInv _ htl htl0
      (by rw [← map_mul, show t * t = 1 from Subtype.ext htt, map_one]) (hπinv t htx)
    have h3 := evenInv_mul_jInv_pow_three _ hρ _ hψ
    have hwB : (((y * t) ^ 3 : ↥(hsNB z s)) : G) ∈ hsB z s :=
      (M.ker _).mp (by rw [map_pow, map_mul, h3])
    have hcomm : (y : G) * t * x' = x' * ((y : G) * t) := by
      calc (y : G) * t * x' = y * (t * x' * (t : G)⁻¹) * t := by group
        _ = y * (x' : G)⁻¹ * t := by rw [htx]
        _ = ((y : G) * (x' : G)⁻¹ * (y : G)⁻¹) * (y * t) := by group
        _ = x' * ((y : G) * t) := by
          rw [show (y : G) * (x' : G)⁻¹ * (y : G)⁻¹ = ((y : G) * x' * (y : G)⁻¹)⁻¹ by group,
            hyx', inv_inv]
    have hw1 := M.eq_one_of_mem_hsB_comm hπx' hwB (by
      rw [Subgroup.coe_pow, Subgroup.coe_mul]
      exact (Commute.pow_left (show Commute ((y : G) * t) x' from hcomm) 3).eq)
    rw [Subgroup.coe_pow, Subgroup.coe_mul] at hw1
    rw [show i * (g * t * g⁻¹) = g * ((y : G) * t) * g⁻¹ by rw [hy]; group, conj_pow, hw1]
    group

end S6Model

end HSSetting

end CFSG.Quasithin.HSType
