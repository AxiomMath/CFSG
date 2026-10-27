module

public import CFSG.Quasithin.H13.L32A770i
public import CFSG.Quasithin.H13.L32A770h
public import CFSG.Quasithin.H13.L32NSet14Gen

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem not_cycle3 {Z : Subgroup G} {t a b : G} (hZ : ∀ v ∈ Z, t * v * t⁻¹ = v) {m : ℕ}
    (hm : t ^ 2 ^ m = 1) (hab : t * a * t⁻¹ * b⁻¹ ∈ Z) (hb : t * b * t⁻¹ * (a * b)⁻¹ ∈ Z)
    (hab2 : t * (a * b) * t⁻¹ * a⁻¹ ∈ Z) : a * b⁻¹ ∈ Z ∨ a * (a * b)⁻¹ ∈ Z := by
  have htrans : ∀ x y w : G, x * y⁻¹ ∈ Z → y * w⁻¹ ∈ Z → x * w⁻¹ ∈ Z := fun x y w h1 h2 => by
    have := mul_mem h1 h2
    rwa [show x * y⁻¹ * (y * w⁻¹) = x * w⁻¹ by group] at this
  have hconj : ∀ x y : G, x * y⁻¹ ∈ Z → t * x * t⁻¹ * (t * y * t⁻¹)⁻¹ ∈ Z := fun x y hxy => by
    rw [show t * x * t⁻¹ * (t * y * t⁻¹)⁻¹ = t * (x * y⁻¹) * t⁻¹ by group, hZ _ hxy]
    exact hxy
  have key : ∀ n : ℕ, (n % 3 = 0 → t ^ n * a * (t ^ n)⁻¹ * a⁻¹ ∈ Z) ∧
      (n % 3 = 1 → t ^ n * a * (t ^ n)⁻¹ * b⁻¹ ∈ Z) ∧
      (n % 3 = 2 → t ^ n * a * (t ^ n)⁻¹ * (a * b)⁻¹ ∈ Z) := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => by simp, fun h => absurd h (by norm_num),
        fun h => absurd h (by norm_num)⟩
    | succ n ih =>
      have e : t ^ (n + 1) * a * (t ^ (n + 1))⁻¹ = t * (t ^ n * a * (t ^ n)⁻¹) * t⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      obtain ⟨ih0, ih1, ih2⟩ := ih
      have hn3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
      refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
      · have h2' : n % 3 = 2 := by omega
        exact htrans _ _ _ (hconj _ _ (ih2 h2')) hab2
      · have h0' : n % 3 = 0 := by omega
        exact htrans _ _ _ (hconj _ _ (ih0 h0')) hab
      · have h1' : n % 3 = 1 := by omega
        exact htrans _ _ _ (hconj _ _ (ih1 h1')) hb
  obtain ⟨-, k1, k2⟩ := key (2 ^ m)
  rw [hm, one_mul, inv_one, mul_one] at k1 k2
  have h3 : ¬ 3 ∣ 2 ^ m := fun hd =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
  have hlt : 2 ^ m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2) with e | e
  · exact Or.inl (k1 e)
  · exact Or.inr (k2 e)

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem inf_V_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h64 : Remark14_7_64) (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) (h8 : Nat.card ↥(u0 T V) = 8) :
    ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ⊓ V = fsuV1 T V := by
  obtain ⟨s, hsW, hsQ, hWs⟩ := N.exists_mem_not_mem h hMod hF h2
  have hsR : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    have := N.uα_le hF
    rw [uα_eq (g := g) (k := k) h hMod] at this
    exact this hsW
  have hV1F := N.v1_le h hMod h63 hF h1222 h1332 h1334 h69 h2
  refine le_antisymm (fun x hx => ?_) (le_inf hV1F hF.V₁_le_Vp)
  obtain ⟨hxF, hxV⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨u, hu, hxu⟩ := (N.mem_sup_iff h hMod hF hsW hWs).mp (Subgroup.mem_sup_left hxF)
  have hcV : u * s * u⁻¹ * s⁻¹ ∈ V := by
    rw [show u * s * u⁻¹ * s⁻¹ = (x * (u * s * u⁻¹ * s⁻¹)⁻¹)⁻¹ * x by group]
    exact mul_mem (inv_mem (hF.V₁_le_Vp hxu)) hxV
  have hc1 := ((h64 G T L V h).2.2.2.1 h8).1 s hsR hsQ u hu hcV
  rw [show x = (x * (u * s * u⁻¹ * s⁻¹)⁻¹) * (u * s * u⁻¹ * s⁻¹) by group]
  exact mul_mem hxu hc1

theorem T_le_normalizer_E (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h64 : Remark14_7_64)
    (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) (h8 : Nat.card ↥(u0 T V) = 8) {s : G}
    (hsW : s ∈ conjSub ((k : G) * g) (fsuU T V)) (hsQ : s ∉ pCoreOf 2 (hz T V))
    (hsT : ∀ t ∈ T, t * s * t⁻¹ * s⁻¹ ∈ pCoreOf 2 (hz T V)) :
    T ≤ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ with hFdef
  set E := fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) with hE
  have hZcard : Nat.card ↥(conjSub ((k : G) * g) (fsuV1 T V)) = 2 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact hF.card_V₁
  obtain ⟨zα, hzα, -, hgenα⟩ := exists_gen_of_card_two hZcard
  have hV1F := N.v1_le h hMod h63 hF h1222 h1332 h1334 h69 h2
  have hZF := N.zα_le h hMod h63 hF h1222 h1332 h1334 h2
  have hFU := N.F_le_U h hMod hF
  have hFW := N.F_le_Uα h hMod hF h2
  have hTF := N.T_le_normalizer_F h hMod h63 hF h1222 h1332 h1334 h69 h2 hsW hsQ hsT
  have hFV := N.inf_V_eq h hMod h63 hF h1222 h1332 h1334 h64 h69 h2 h8
  have hTH : T ≤ hz T V := hF.T_le_H
  have hzαF : zα ∈ F := hZF hzα
  obtain ⟨hUc, hUe⟩ := F7.isElemAbelian_iff.mp (isElemAbelian_fsuU_of h hMod)
  have hsq : ∀ x ∈ fsuU T V, x * x = 1 := fun x hx => by rw [← sq]; exact hUe x hx
  have hconjF : ∀ t ∈ T, ∀ x ∈ F, t * x * t⁻¹ ∈ F := fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.mp (hTF ht) x).mp hx
  have hred : ∀ t ∈ T, t * zα * t⁻¹ ∈ E → t ∈ Subgroup.normalizer (E : Set G) := by
    intro t ht hmem
    have htH := hTH ht
    rw [← conjSub_eq_self_iff]
    refine conjSub_eq_of_le ?_
    rw [hE, conjSub_sup, conjSub_eq_self_iff.mpr (hF.H_normalizes_V₁ htH)]
    refine sup_le le_sup_left ?_
    rintro _ ⟨y, hy, rfl⟩
    show t * y * t⁻¹ ∈ E
    rcases hgenα y hy with rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · exact hmem
  intro t ht
  by_contra hnot
  have hf : t * zα * t⁻¹ ∉ E := fun h' => hnot (hred t ht h')
  have hf' : t⁻¹ * zα * t ∉ E := fun h' => hnot (by
    have := hred t⁻¹ (inv_mem ht) (by simpa using h')
    simpa using inv_mem this)
  set f := t * zα * t⁻¹ with hfdef
  set f' := t⁻¹ * zα * t with hf'def
  have hfF : f ∈ F := hconjF t ht zα hzαF
  have hf'F : f' ∈ F := by simpa using hconjF t⁻¹ (inv_mem ht) zα hzαF
  obtain ⟨c, hcQ, hcH, hcf⟩ :=
    N.exists_transvection h hMod h63 hF h1222 h1332 h1334 h13314 h64 h69 h2 hfF hf
  obtain ⟨d, hdQ, hdH, hdf⟩ :=
    N.exists_transvection h hMod h63 hF h1222 h1332 h1334 h13314 h64 h69 h2 hf'F hf'
  have hact : ∀ c ∈ conjSub ((k : G) * g) (pCoreOf 2 (hz T V)), ∀ x ∈ F,
      c * x * c⁻¹ ≠ x → c * x * c⁻¹ = zα * x := by
    intro c hc x hx hne
    rcases hgenα _ (comm_mem_zα h hMod hF hc (hFW hx)) with e | e
    · exact absurd (by
        calc c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x := by group
          _ = x := by rw [e, one_mul]) hne
    · calc c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x := by group
        _ = zα * x := by rw [e]
  have hQαC : conjSub ((k : G) * g) (pCoreOf 2 (hz T V)) ≤
      Subgroup.centralizer (conjSub ((k : G) * g) (fsuV1 T V) : Set G) := by
    rw [conjSub_centralizer]
    exact conjSub_mono _ (pCoreOf_le 2 _)
  have hfixα : ∀ c ∈ conjSub ((k : G) * g) (pCoreOf 2 (hz T V)), c * zα * c⁻¹ = zα :=
    fun c hc => by
      have := Subgroup.mem_centralizer_iff.mp (hQαC hc) zα hzα
      rw [← this, mul_inv_cancel_right]
  have hcf2 : c * f * c⁻¹ = zα * f := hact c hcQ f hfF hcf
  have hdf2 : d * f' * d⁻¹ = zα * f' := hact d hdQ f' hf'F hdf
  have hczα := hfixα c hcQ
  have hdzα := hfixα d hdQ
  have hfU : f ∈ fsuU T V := hFU hfF
  have hzαU : zα ∈ fsuU T V := hFU hzαF
  set w := c * (t * d * t⁻¹) with hw
  have hc'zα : t * d * t⁻¹ * zα * (t * d * t⁻¹)⁻¹ = f * zα := by
    calc t * d * t⁻¹ * zα * (t * d * t⁻¹)⁻¹ = t * (d * f' * d⁻¹) * t⁻¹ := by
          rw [hf'def]; group
      _ = t * (zα * f') * t⁻¹ := by rw [hdf2]
      _ = f * zα := by rw [hfdef, hf'def]; group
  have hc'f : t * d * t⁻¹ * f * (t * d * t⁻¹)⁻¹ = f := by
    calc t * d * t⁻¹ * f * (t * d * t⁻¹)⁻¹ = t * (d * zα * d⁻¹) * t⁻¹ := by rw [hfdef]; group
      _ = f := by rw [hdzα]
  have hwzα : w * zα * w⁻¹ = f := by
    calc w * zα * w⁻¹ = c * (t * d * t⁻¹ * zα * (t * d * t⁻¹)⁻¹) * c⁻¹ := by rw [hw]; group
      _ = (c * f * c⁻¹) * (c * zα * c⁻¹) := by rw [hc'zα]; group
      _ = zα * (f * zα) := by rw [hcf2, hczα, mul_assoc]
      _ = zα * zα * f := by rw [hUc f hfU zα hzαU, mul_assoc]
      _ = f := by rw [hsq zα hzαU, one_mul]
  have hwf : w * f * w⁻¹ = zα * f := by
    calc w * f * w⁻¹ = c * (t * d * t⁻¹ * f * (t * d * t⁻¹)⁻¹) * c⁻¹ := by rw [hw]; group
      _ = zα * f := by rw [hc'f, hcf2]
  have hwH : w ∈ hz T V :=
    mul_mem hcH (mul_mem (mul_mem (hTH ht) hdH) (inv_mem (hTH ht)))
  have hQαN : ∀ c ∈ conjSub ((k : G) * g) (pCoreOf 2 (hz T V)),
      c ∈ Subgroup.normalizer (F : Set G) := by
    intro c hc
    rw [← conjSub_eq_self_iff]
    refine conjSub_eq_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    show c * x * c⁻¹ ∈ F
    rw [show c * x * c⁻¹ = (c * x * c⁻¹ * x⁻¹) * x by group]
    exact mul_mem (hZF (comm_mem_zα h hMod hF hc (hFW hx))) hx
  have hwN : w ∈ Subgroup.normalizer (F : Set G) :=
    mul_mem (hQαN c hcQ) (mul_mem (mul_mem (hTF ht) (hQαN d hdQ)) (inv_mem (hTF ht)))
  obtain ⟨s₀, hs₀W, hs₀Q, -⟩ := N.exists_mem_not_mem h hMod hF h2
  have hsup := N.sup_u0 h hMod h63 hF h1222 h1332 h1334 hs₀W hs₀Q
  have hwVU : w ∈ Subgroup.normalizer ((V ⊔ u0 T V : Subgroup G) : Set G) := by
    rw [← hsup, ← conjSub_eq_self_iff, conjSub_sup, conjSub_eq_self_iff.mpr hwN,
      conjSub_eq_self_iff.mpr (hz_le_normalizer_u0 h hMod hwH)]
  have hwP := normalizer_sup_u0_le h hMod h63 hF h1222 h1332 h1334 ⟨hwH, hwVU⟩
  have hwV : w ∈ Subgroup.normalizer (V : Set G) := hF.L₁T_normalizes_Vp hwP
  have hwU0 : w ∈ Subgroup.normalizer (u0 T V : Set G) := hz_le_normalizer_u0 h hMod hwH
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ S14.T_Lp] at hwP
  obtain ⟨l, hl, t', ht', hwlt⟩ := hwP
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hUH : fsuU T V ≤ hz T V := by
    rw [fsuU_eq_conjClosure_hz hMod h]
    exact hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)
  have hVN : V ≤ Subgroup.normalizer (u0 T V : Set G) :=
    (hVU.trans hUH).trans (hz_le_normalizer_u0 h hMod)
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVN
  have hzαVU : zα ∈ V ⊔ u0 T V := hsup ▸ Subgroup.mem_sup_left hzαF
  have hfVU : f ∈ V ⊔ u0 T V := hsup ▸ Subgroup.mem_sup_left hfF
  rw [← SetLike.mem_coe, hcoe] at hzαVU hfVU
  obtain ⟨vα, hvα, uα, huα, hzαe⟩ := hzαVU
  obtain ⟨vf, hvf, uf, huf, hfe⟩ := hfVU
  have hVU0 := inf_u0_eq h hMod h63 hF
  have hmemV1 : ∀ x ∈ V, x ∈ u0 T V → x ∈ fsuV1 T V := fun x hx hx' => by
    rw [← hVU0]
    exact ⟨hx, hx'⟩
  have hcompo : ∀ (v₁ v₂ : G) (u₁ u₂ : G), v₁ ∈ V → v₂ ∈ V → u₁ ∈ u0 T V → u₂ ∈ u0 T V →
      w * (v₁ * u₁) * w⁻¹ = v₂ * u₂ → w * u₁ * w⁻¹ * u₂⁻¹ ∈ fsuV1 T V := by
    intro v₁ v₂ u₁ u₂ hv₁ hv₂ hu₁ hu₂ he
    have hwv := (Subgroup.mem_normalizer_iff.mp hwV v₁).mp hv₁
    have hwu := (Subgroup.mem_normalizer_iff.mp hwU0 u₁).mp hu₁
    have e : w * u₁ * w⁻¹ * u₂⁻¹ = (w * v₁ * w⁻¹)⁻¹ * v₂ := by
      calc w * u₁ * w⁻¹ * u₂⁻¹ = (w * v₁ * w⁻¹)⁻¹ * (w * (v₁ * u₁) * w⁻¹) * u₂⁻¹ := by group
        _ = (w * v₁ * w⁻¹)⁻¹ * (v₂ * u₂) * u₂⁻¹ := by rw [he]
        _ = (w * v₁ * w⁻¹)⁻¹ * v₂ := by group
    refine hmemV1 _ ?_ (mul_mem hwu (inv_mem hu₂))
    rw [e]
    exact mul_mem (inv_mem hwv) hv₂
  have hA : w * uα * w⁻¹ * uf⁻¹ ∈ fsuV1 T V :=
    hcompo vα vf uα uf hvα hvf huα huf (by
      show w * (vα * uα) * w⁻¹ = vf * uf
      rw [show vα * uα = zα from hzαe, show vf * uf = f from hfe, hwzα])
  have hcα : uα * vf = vf * uα := hUc uα (hU0U huα) vf (hVU hvf)
  have hB : w * uf * w⁻¹ * (uα * uf)⁻¹ ∈ fsuV1 T V := by
    refine hcompo vf (vα * vf) uf (uα * uf) hvf (mul_mem hvα hvf) huf (mul_mem huα huf) ?_
    show w * (vf * uf) * w⁻¹ = vα * vf * (uα * uf)
    rw [show vf * uf = f from hfe, hwf, ← show vα * uα = zα from hzαe,
      ← show vf * uf = f from hfe]
    calc vα * uα * (vf * uf) = vα * (uα * vf) * uf := by group
      _ = vα * (vf * uα) * uf := by rw [hcα]
      _ = vα * vf * (uα * uf) := by group
  have hlK : l ∈ kz T V := l1_le_kz h hMod hl
  have ht'H : t' ∈ hz T V := hTH ht'
  have hlact : ∀ u ∈ u0 T V, t' * u * t'⁻¹ * (w * u * w⁻¹)⁻¹ ∈ fsuV1 T V := by
    intro u hu
    have hu' : t' * u * t'⁻¹ ∈ u0 T V :=
      (Subgroup.mem_normalizer_iff.mp (hz_le_normalizer_u0 h hMod ht'H) u).mp hu
    have h1 := hu'.2.2 l hlK
    rw [← hwlt]
    rwa [show t' * u * t'⁻¹ * (l * t' * u * (l * t')⁻¹)⁻¹ =
      t' * u * t'⁻¹ * l * (t' * u * t'⁻¹)⁻¹ * l⁻¹ by group]
  have htrans : ∀ x y z : G, x * y⁻¹ ∈ fsuV1 T V → y * z⁻¹ ∈ fsuV1 T V →
      x * z⁻¹ ∈ fsuV1 T V := fun x y z h1 h2 => by
    have := mul_mem h1 h2
    rwa [show x * y⁻¹ * (y * z⁻¹) = x * z⁻¹ by group] at this
  have hA' : t' * uα * t'⁻¹ * uf⁻¹ ∈ fsuV1 T V := htrans _ _ _ (hlact uα huα) hA
  have hB' : t' * uf * t'⁻¹ * (uα * uf)⁻¹ ∈ fsuV1 T V := htrans _ _ _ (hlact uf huf) hB
  have hufU := hU0U huf
  have huαU := hU0U huα
  have hC' : t' * (uα * uf) * t'⁻¹ * uα⁻¹ ∈ fsuV1 T V := by
    have hb₁U : t' * uf * t'⁻¹ * (uα * uf)⁻¹ ∈ fsuU T V :=
      (fsuV1_le_u0 h hMod).trans hU0U hB'
    have e : t' * (uα * uf) * t'⁻¹ * uα⁻¹ =
        (t' * uα * t'⁻¹ * uf⁻¹) * (t' * uf * t'⁻¹ * (uα * uf)⁻¹) := by
      calc t' * (uα * uf) * t'⁻¹ * uα⁻¹ = (t' * uα * t'⁻¹ * uf⁻¹) *
            (uf * (t' * uf * t'⁻¹ * (uα * uf)⁻¹)) * (uα * uf) * uα⁻¹ := by group
        _ = (t' * uα * t'⁻¹ * uf⁻¹) *
            ((t' * uf * t'⁻¹ * (uα * uf)⁻¹) * uf) * (uα * uf) * uα⁻¹ := by
              rw [hUc uf hufU _ hb₁U]
        _ = (t' * uα * t'⁻¹ * uf⁻¹) * (t' * uf * t'⁻¹ * (uα * uf)⁻¹) *
            (uf * uα) * uf * uα⁻¹ := by group
        _ = (t' * uα * t'⁻¹ * uf⁻¹) * (t' * uf * t'⁻¹ * (uα * uf)⁻¹) *
            (uα * uf) * uf * uα⁻¹ := by rw [hUc uf hufU uα huαU]
        _ = (t' * uα * t'⁻¹ * uf⁻¹) * (t' * uf * t'⁻¹ * (uα * uf)⁻¹) *
            uα * (uf * uf) * uα⁻¹ := by group
        _ = (t' * uα * t'⁻¹ * uf⁻¹) * (t' * uf * t'⁻¹ * (uα * uf)⁻¹) := by
              rw [hsq uf hufU]; group
    rw [e]
    exact mul_mem hA' hB'
  have hZ : ∀ v ∈ fsuV1 T V, t' * v * t'⁻¹ = v := fun v hv => by
    have := Subgroup.mem_centralizer_iff.mp ht'H v hv
    rw [← this, mul_inv_cancel_right]
  obtain ⟨m, hm⟩ := h.fsu.sylow.1 ⟨t', ht'⟩
  have hm' : t' ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hfE : f ∈ E → False := hf
  rcases not_cycle3 hZ hm' hA' hB' hC' with e | e
  · apply hfE
    have h1 : zα * f⁻¹ ∈ fsuV1 T V := by
      rw [← hFV]
      refine Subgroup.mem_inf.mpr ⟨mul_mem hzαF (inv_mem hfF), ?_⟩
      rw [← show vα * uα = zα from hzαe, ← show vf * uf = f from hfe,
        show vα * uα * (vf * uf)⁻¹ = vα * (uα * uf⁻¹) * vf⁻¹ by group]
      exact mul_mem (mul_mem hvα (hF.V₁_le_Vp e)) (inv_mem hvf)
    rw [show f = (zα * f⁻¹)⁻¹ * zα by group]
    exact mul_mem (Subgroup.mem_sup_left (inv_mem h1)) (Subgroup.mem_sup_right hzα)
  · apply hfE
    have huf1 : uf ∈ fsuV1 T V := by
      have h1 : uα * (uα * uf)⁻¹ = uf⁻¹ := by
        rw [mul_inv_rev, ← mul_assoc, hUc uα huαU uf⁻¹ (inv_mem hufU), mul_assoc,
          mul_inv_cancel, mul_one]
      rw [h1] at e
      simpa using inv_mem e
    have hfV : f ∈ V := by
      rw [← show vf * uf = f from hfe]
      exact mul_mem hvf (hF.V₁_le_Vp huf1)
    have hfV1 : f ∈ fsuV1 T V := by
      rw [← hFV]
      exact Subgroup.mem_inf.mpr ⟨hfF, hfV⟩
    exact Subgroup.mem_sup_left hfV1

end Not1471

end CFSG.Quasithin.H13.L32A
