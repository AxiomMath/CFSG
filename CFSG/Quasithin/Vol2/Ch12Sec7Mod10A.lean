module

public import CFSG.Quasithin.Background.E6Hyp
public import CFSG.Quasithin.Vol2.Ch12Sec7L22a
public import CFSG.Quasithin.Vol2.Ch12Sec7ModCert2
public import CFSG.Quasithin.Vol2.Ch12Sec7ModI

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem conjugate_eq_or_of_1222 (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥ := by
  have hy := h.hyp
  obtain ⟨-, -, hall⟩ := ((h1222 G T hy.simple hy.nonabelian hy.qtke hy.sylow).resolve_left
    hy.notAlt) L hy.maximal hy.faithful hy.quasisimple
  obtain ⟨-, hTI, -⟩ := hall V hy.irrPlus
  exact hTI m hm

theorem mem_normalizer_of_mem_inf_centralizer (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V)
    {U : Subgroup G} (hUV : U ≤ V) (hU : U ≠ ⊥) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G)) :
    m ∈ Subgroup.normalizer (V : Set G) := by
  obtain ⟨hmM, hmU⟩ := Subgroup.mem_inf.1 hm
  rcases conjugate_eq_or_of_1222 h1222 h hmM with he | he
  · apply normalizer_of_maps
    intro w hw
    have hw' : w ∈ CFSG.conjugate V m := he.symm ▸ hw
    obtain ⟨w', hw'V, hww'⟩ := Subgroup.mem_map.1 hw'
    have e : m * w * m⁻¹ = w' := by
      rw [← hww']
      simp [mul_assoc]
    rw [e]
    exact hw'V
  · exfalso
    apply hU
    rw [eq_bot_iff, ← he]
    intro u hu
    refine Subgroup.mem_inf.2 ⟨hUV hu, Subgroup.mem_map.2 ⟨u, hUV hu, ?_⟩⟩
    have hc := Subgroup.mem_centralizer_iff.1 hmU u hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc m⁻¹ * u * m = m⁻¹ * (u * m) := by group
      _ = m⁻¹ * (m * u) := by rw [hc]
      _ = u := by group

theorem isPGroup_V' (h : Hyp1271 G T L V) : IsPGroup 2 V :=
  fun v => ⟨1, Subtype.ext (by simpa using sq_eq_one_of_mem h.hyp v.2)⟩

theorem normalizer_V_le_M (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hyp := h.hyp
  obtain ⟨-, -, hTV⟩ := card_eq_of_1222 h1222 h
  have h3 := (h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).2 L hyp.maximal
    hyp.quasisimple
  rw [hyp.conjClosure_eq] at h3
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h3
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hyp.irrPlus.2.2.1 hTV
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer (V : Set G))
    ⟨V, hyp.irrPlus.2.1, isPGroup_V' h, rfl⟩
  have hM'eq : M' = Subgroup.normalizer (L : Set G) := huniq M' hM' (hLTV.trans hle)
  exact hM'eq ▸ hle

omit [Finite G] in
theorem conjClosure_self {Z H : Subgroup G} (hN : H ≤ Subgroup.normalizer (Z : Set G)) :
    conjClosure Z H = Z :=
  le_antisymm (conjClosure_le fun _ hk z hz => (Subgroup.mem_normalizer_iff.mp (hN hk) z).mp hz)
    (le_conjClosure Z H)

theorem pCoreOf_sup_eq_1271 (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight)
    (hyp : Hyp1223 G T L V) : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G) := by
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨-, hTV, -, hfsu⟩, -, -, -⟩ := hall V hyp.irrPlus
  obtain ⟨-, -, hO⟩ := h3228 G T L V hfsu
  rwa [hyp.conjClosure_eq, conjClosure_self hTV] at hO

theorem hypE61_1271 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight)
    (h : Hyp1271 G T L V) : E6.HypE61 T (Subgroup.normalizer (L : Set G)) V := by
  have hyp := h.hyp
  obtain ⟨hcomm, hV64, hTV⟩ := card_eq_of_1222 h1222 h
  have hVT := le_T_of_1222 h1222 h
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hV1 : V ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hV64
    norm_num at hV64
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨hmax, -, huniq⟩, -, -, -, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at hmax huniq
  have hLT : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hyp.normalizes
  have hQ : L ⊔ T ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    rw [← pCoreOf_sup_eq_1271 h1222 h3228 hyp]
    exact LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hLTX : L ⊔ T ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ⊓
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) :=
    le_inf hQ (le_inf hLT (sup_le hLV hTV))
  refine
    { simple := hyp.simple
      nonabelian := hyp.nonabelian
      qtke := hyp.qtke
      sylow := hyp.sylow
      inM := ⟨hmax, hyp.normalizes⟩
      ne_bot := hV1
      isElemAbelian := ⟨hcomm, fun v hv => sq_eq_one_of_mem hyp hv⟩
      le := hVT
      normal := hTV
      tiSet := ⟨hVT.trans hyp.normalizes, fun g hg hgN => ?_⟩
      unique := ⟨⟨hmax, inf_le_right.trans inf_le_left⟩, fun M' hM' =>
        huniq M' hM'.1 (hLTX.trans hM'.2)⟩ }
  rcases conjugate_eq_or_of_1222 h1222 h hg with he | he
  · exfalso
    apply hgN
    apply normalizer_of_maps
    intro w hw
    have hw' : w ∈ CFSG.conjugate V g := he.symm ▸ hw
    obtain ⟨w', hw'V, hww'⟩ := Subgroup.mem_map.1 hw'
    have e : g * w * g⁻¹ = w' := by
      rw [← hww']
      simp [mul_assoc]
    rw [e]
    exact hw'V
  · exact he

section Fix

variable {W : Type} [CommGroup W]

theorem fixCount_eq (B : B6) :
    fixCount B = ((List.range 64).filter fun c => B.app c == c).length := rfl

theorem nodup_fixed (B : B6) : ((List.range 64).filter fun c => B.app c == c).Nodup :=
  List.nodup_range.filter _

theorem card_fixed (B : B6) :
    Nat.card {c : ℕ // c ∈ (List.range 64).filter fun c => B.app c == c} = fixCount B := by
  classical
  have e2 : {c : ℕ // c ∈ (List.range 64).filter fun c => B.app c == c} ≃
      ↥((List.range 64).filter fun c => B.app c == c).toFinset :=
    Equiv.subtypeEquivRight fun c => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup (nodup_fixed B),
    fixCount_eq]

theorem mem_fixed {B : B6} {c : ℕ} :
    c ∈ (List.range 64).filter (fun c => B.app c == c) ↔ c < 64 ∧ B.app c = c := by
  simp [List.mem_filter]

end Fix

variable [IsMulCommutative ↥V]

omit [Finite G] in
theorem card_le_fixCount {C : Coding ↥V} {U : Subgroup G} (hUV : U ≤ V) {B : B6}
    (hfix : ∀ u : ↥V, (u : G) ∈ U → B.app (C.cd u) = C.cd u) : Nat.card U ≤ fixCount B := by
  have hinj : Function.Injective (fun u : ↥U =>
      (⟨C.cd ⟨u, hUV u.2⟩, mem_fixed.2 ⟨C.cd_lt _, hfix _ u.2⟩⟩ :
        {c : ℕ // c ∈ (List.range 64).filter fun c => B.app c == c})) := by
    intro a b hab
    have := C.cd_injective (congrArg Subtype.val hab)
    exact Subtype.ext (congrArg (fun x : ↥V => (x : G)) this)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [card_fixed] at this

omit [Finite G] in
theorem mem_of_fixCount_le {C : Coding ↥V} {U : Subgroup G} (hUV : U ≤ V) {B : B6}
    (hfix : ∀ u : ↥V, (u : G) ∈ U → B.app (C.cd u) = C.cd u) (hcard : fixCount B ≤ Nat.card U)
    {c : ℕ} (hc : c < 64) (hcB : B.app c = c) : (C.dc c : G) ∈ U := by
  set f := (fun u : ↥U =>
      (⟨C.cd ⟨u, hUV u.2⟩, mem_fixed.2 ⟨C.cd_lt _, hfix _ u.2⟩⟩ :
        {c : ℕ // c ∈ (List.range 64).filter fun c => B.app c == c})) with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have := C.cd_injective (congrArg Subtype.val hab)
    exact Subtype.ext (congrArg (fun x : ↥V => (x : G)) this)
  have hbij := hinj.bijective_of_nat_card_le (by rw [card_fixed]; exact hcard)
  obtain ⟨u, hu⟩ := hbij.2 ⟨c, mem_fixed.2 ⟨hc, hcB⟩⟩
  have e : C.cd ⟨u, hUV u.2⟩ = c := congrArg Subtype.val hu
  have : C.dc c = ⟨u, hUV u.2⟩ := by rw [← e, C.dc_cd]
  rw [this]
  exact u.2

theorem exists_invol_pow {W : Type} [CommGroup W]
    {C : Coding W} {a : MulAut W} (ha : C.cB a ∈ nm6) (ha1 : a ≠ 1)
    (h8 : 8 ≤ fixCount (C.cB a)) : ∃ k : ℕ, a ^ k ≠ 1 ∧ (a ^ k) ^ 2 = 1 := by
  have h60 : a ^ 60 = 1 := (C.pow_eq_one_iff a 60).2 (cert4_pow60 _ ha)
  have h15 : a ^ 15 ≠ 1 := by
    intro e
    have hB15 : (C.cB a).pow 15 = B6.id := (C.pow_eq_one_iff a 15).1 e
    have := cert4_odd_fix8 _ ha hB15 (fun hid => ha1 (C.cB_eq_one.1 hid))
    omega
  by_cases h30 : (a ^ 15) ^ 2 = 1
  · exact ⟨15, h15, h30⟩
  · refine ⟨30, by rwa [show 30 = 15 * 2 from rfl, pow_mul], ?_⟩
    rw [← pow_mul, show 30 * 2 = 60 from rfl, h60]

theorem pow_apply_eq_self {W : Type} [CommGroup W] {a : MulAut W} {w : W} (h : a w = w) :
    ∀ k : ℕ, (a ^ k) w = w
  | 0 => rfl
  | k + 1 => by rw [pow_succ, MulAut.mul_apply, h, pow_apply_eq_self h k]

end CFSG.Quasithin.H13.S127.Mod

end
