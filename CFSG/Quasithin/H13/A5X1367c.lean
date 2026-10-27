module

public import CFSG.Quasithin.H13.A5X1367a
public import CFSG.Quasithin.H13.A5X1367b
public import CFSG.Quasithin.H13.A5S136i

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem Tv_le_normalizer_Lv : S.Tv ≤ Subgroup.normalizer (S.Lv : Set G) := by
  refine le_normalizer_oTwoRes fun u hu => ?_
  have huL : u ∈ Subgroup.normalizer (L : Set G) := S.T_le_NL hu.1
  have huG : u ∈ Subgroup.centralizer ({S.v12} : Set G) := hu.2
  set Gv := Subgroup.centralizer ({S.v12} : Set G)
  refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
  · exact ⟨(Subgroup.mem_normalizer_iff.mp huL x).mp hx.1,
      Gv.mul_mem (Gv.mul_mem huG hx.2) (Gv.inv_mem huG)⟩
  · refine ⟨?_, Gv.mul_mem (Gv.mul_mem (Gv.inv_mem huG) hx.2) huG⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huL) x).mp hx.1
    simpa using this

theorem Tv_le_Gv : S.Tv ≤ Subgroup.centralizer ({S.v12} : Set G) := inf_le_right

theorem exists_Lv_c234_odd : ∃ l : ↥(Subgroup.normalizer (V : Set G)), (l : G) ∈ S.Lv ∧
    Odd (orderOf (l : G)) ∧ (S.frame.ρ l = c234 ∨ S.frame.ρ l = c234⁻¹) := by
  obtain ⟨l₀, hl₀L, hl₀σ⟩ := (S.frame.image_L c234).2 c234_sign
  have hl₀ : (l₀ : G) ∈ L ⊓ Subgroup.centralizer ({S.v12} : Set G) :=
    ⟨hl₀L, S.mem_centralizer_v12 l₀ (by rw [hl₀σ]; exact pact_c234_E12)⟩
  obtain ⟨j, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (l₀ : G)).ne'
  set l : ↥(Subgroup.normalizer (V : Set G)) := l₀ ^ 2 ^ j with hl
  have hlG : (l : G) = (l₀ : G) ^ 2 ^ j := by rw [hl, Subgroup.coe_pow]
  have hord : orderOf (l : G) = m := by
    rw [hlG, orderOf_pow_of_dvd (by positivity) ⟨m, hn⟩]
    rw [hn]
    exact Nat.mul_div_cancel_left m (by positivity)
  have hlm : (l : G) ^ m = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hlLv : (l : G) ∈ S.Lv := by
    refine Subgroup.subset_closure ⟨?_, m, hm, hlm⟩
    rw [hlG]
    exact Subgroup.pow_mem _ hl₀ _
  refine ⟨l, hlLv, hord ▸ hm, ?_⟩
  rw [hl, map_pow, hl₀σ]
  exact c234_pow_two_pow j

theorem rho_Lv_cases (l : ↥(Subgroup.normalizer (V : Set G))) (hl : (l : G) ∈ S.Lv) :
    S.frame.ρ l = 1 ∨ S.frame.ρ l = c234 ∨ S.frame.ρ l = c234⁻¹ := by
  obtain ⟨_, h⟩ := S.rho_Lv hl
  exact h

theorem two_pow_of_Lv_of_rho (l : ↥(Subgroup.normalizer (V : Set G))) (hl : (l : G) ∈ S.Lv)
    (hρ : S.frame.ρ l = 1) : ∃ k : ℕ, (l : G) ^ 2 ^ k = 1 := by
  have hlL : (l : G) ∈ L := (oTwoRes_le _ hl).1
  have hlC : (l : G) ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h := (S.conj_eq_iff l ⟨u, hu⟩).2 (by rw [hρ, map_one, MulAut.one_apply])
    calc u * (l : G) = (l : G) * u * (l : G)⁻¹ * (l : G) := by rw [h]
      _ = (l : G) * u := by group
  have hO : (l : G) ∈ pCoreOf 2 (L ⊔ T) := by
    rw [← S.cLT]
    exact ⟨Subgroup.mem_sup_left hlL, hlC⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T) ⟨_, hO⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem decomp_unique {A : Type} [Group A] {U₁ W : Subgroup A} (hU₁W : U₁ ⊓ W = ⊥)
    {a b a' b' : A} (ha : a ∈ U₁) (hb : b ∈ W) (ha' : a' ∈ U₁) (hb' : b' ∈ W)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hm : a'⁻¹ * a ∈ U₁ ⊓ W :=
    ⟨U₁.mul_mem (U₁.inv_mem ha') ha, h1 ▸ W.mul_mem hb' (W.inv_mem hb)⟩
  rw [hU₁W, Subgroup.mem_bot, inv_mul_eq_one] at hm
  refine ⟨hm.symm, ?_⟩
  rw [hm] at h
  exact mul_left_cancel h

theorem autOn_le_GvS {H : Subgroup G} (hH : H ≤ Subgroup.centralizer ({S.v12} : Set G)) :
    autOn H S.Uv ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv := by
  intro a ha
  obtain ⟨g, hg, rfl⟩ := ha
  exact ⟨g, Subgroup.mem_subgroupOf.mpr (hH (Subgroup.mem_subgroupOf.mp hg)), rfl⟩

theorem exists_moved_U₁ (hUe : IsElemAbelian 2 S.Uv) {Y : Subgroup (MulAut ↥S.Uv)}
    (hYG : Y ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)
    (hYn : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (Y : Set (MulAut ↥S.Uv)))
    (hY1 : Y ≠ ⊥) {U₁ W : Subgroup ↥S.Uv}
    (hdec : ∀ u : ↥S.Uv, ∃ a ∈ U₁, ∃ w ∈ W, u = a * w) (hU₁W : U₁ ⊓ W = ⊥)
    (hYW : ∀ y ∈ Y, ∀ w ∈ W, y w = w) (hYU : ∀ u ∈ U₁, (∀ y ∈ Y, y u = u) → u = 1)
    (hGU : ∀ g ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv, ∀ u ∈ U₁, g u ∈ U₁)
    (hGW : ∀ g ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv, ∀ w ∈ W, g w ∈ W)
    (l₀ : ↥(Subgroup.normalizer (V : Set G))) (hl₀Lv : (l₀ : G) ∈ S.Lv)
    (hl₀σ : S.frame.ρ l₀ = c234 ∨ S.frame.ρ l₀ = c234⁻¹)
    (hl₀N : (l₀ : G) ∈ Subgroup.normalizer (S.Uv : Set G)) :
    ∃ e ∈ U₁, conjAct S.Uv ⟨l₀, hl₀N⟩ e ≠ e := by
  set lS : MulAut ↥S.Uv := conjAct S.Uv ⟨l₀, hl₀N⟩ with hlS
  have hlSG : lS ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv :=
    S.autOn_le_GvS S.Lv_le_Gv ⟨⟨l₀, hl₀N⟩, Subgroup.mem_subgroupOf.mpr hl₀Lv, rfl⟩
  have hcomm : ∀ a b : ↥S.Uv, a * b = b * a := fun a b => hUe.1.is_comm.comm a b
  have hsq : ∀ a : ↥S.Uv, a * a = 1 := fun a => by
    have h := hUe.2 (a : G) a.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, h, Subgroup.coe_one])
  obtain ⟨y₀, hy₀Y, hy₀z⟩ := S.exists_apply_ne_zU_of_normal hYn hY1
  obtain ⟨z₁, hz₁, zw, hzw, hzdec⟩ := hdec S.zU
  have hv := S.vU_eq_mul_conjAct l₀ hl₀σ hl₀N
  rw [← hlS] at hv
  by_contra hcon
  push Not at hcon
  have hlinv : ∀ e ∈ U₁, lS⁻¹ e = e := fun e he => by
    conv_lhs => rw [← hcon e he]
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hw' : zw * lS zw * lS⁻¹ zw ∈ W :=
    W.mul_mem (W.mul_mem hzw (hGW _ hlSG _ hzw)) (hGW _ (Subgroup.inv_mem _ hlSG) _ hzw)
  have hvdec : S.vU = z₁ * (zw * lS zw * lS⁻¹ zw) := by
    rw [hv, hzdec, map_mul, map_mul, hcon z₁ hz₁, hlinv z₁ hz₁]
    calc z₁ * zw * (z₁ * lS zw) * (z₁ * lS⁻¹ zw)
        = z₁ * (zw * z₁) * lS zw * (z₁ * lS⁻¹ zw) := by group
      _ = z₁ * (z₁ * zw) * lS zw * (z₁ * lS⁻¹ zw) := by rw [hcomm zw z₁]
      _ = (z₁ * z₁) * (zw * lS zw * z₁) * lS⁻¹ zw := by group
      _ = (z₁ * z₁) * (z₁ * (zw * lS zw)) * lS⁻¹ zw := by rw [hcomm (zw * lS zw) z₁]
      _ = z₁ * (zw * lS zw * lS⁻¹ zw) := by rw [hsq, one_mul]; group
  apply hy₀z
  have hfix : ∀ y ∈ Y, y z₁ = z₁ := by
    intro y hy
    have h1 := S.apply_vU (hYG hy)
    rw [hvdec, map_mul, hYW y hy _ hw'] at h1
    exact (decomp_unique hU₁W (hGU _ (hYG hy) _ hz₁) hw' hz₁ hw' h1).1
  have hz₁1 := hYU z₁ hz₁ hfix
  rw [hzdec, hz₁1, one_mul]
  exact hYW y₀ hy₀Y zw hzw

theorem exists_d_of_three (hUe : IsElemAbelian 2 S.Uv) {U₁ W : Subgroup ↥S.Uv}
    (hU₁ : Nat.card U₁ = 4) (hdec : ∀ u : ↥S.Uv, ∃ a ∈ U₁, ∃ w ∈ W, u = a * w)
    (l₀ : ↥(Subgroup.normalizer (V : Set G))) (hl₀Lv : (l₀ : G) ∈ S.Lv)
    (hl₀odd : Odd (orderOf (l₀ : G)))
    (hl₀N : (l₀ : G) ∈ Subgroup.normalizer (S.Uv : Set G))
    (hlU₁ : ∀ u ∈ U₁, conjAct S.Uv ⟨l₀, hl₀N⟩ u ∈ U₁)
    (hlW : ∀ w ∈ W, conjAct S.Uv ⟨l₀, hl₀N⟩ w ∈ W)
    (hlU : ∃ e ∈ U₁, conjAct S.Uv ⟨l₀, hl₀N⟩ e ≠ e)
    {s : MulAut ↥S.Uv} (hs : s ∈ autOn S.Tv S.Uv) (hsU₁ : ∀ u ∈ U₁, s u ∈ U₁)
    (hsW : ∀ w ∈ W, s w = w) (hsU : ∃ u ∈ U₁, s u ≠ u) :
    ∃ d ∈ autOn S.Lv S.Uv, (∀ w ∈ W, d w = w) ∧ (∀ e ∈ U₁, d e = conjAct S.Uv ⟨l₀, hl₀N⟩ e) ∧
      d ^ 3 = 1 ∧ d ≠ 1 := by
  set GS := autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv with hGS
  set lS : MulAut ↥S.Uv := conjAct S.Uv ⟨l₀, hl₀N⟩ with hlS
  have hsq : ∀ a : ↥S.Uv, a * a = 1 := fun a => by
    have h := hUe.2 (a : G) a.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, h, Subgroup.coe_one])
  have hlSL : lS ∈ autOn S.Lv S.Uv := ⟨⟨l₀, hl₀N⟩, Subgroup.mem_subgroupOf.mpr hl₀Lv, rfl⟩
  have hlSG : lS ∈ GS := S.autOn_le_GvS S.Lv_le_Gv hlSL
  have hlSodd : Odd (orderOf lS) := by
    refine Odd.of_dvd_nat hl₀odd ?_
    have h1 := orderOf_map_dvd (conjAct S.Uv)
      (⟨l₀, hl₀N⟩ : ↥(Subgroup.normalizer (S.Uv : Set G)))
    rwa [Subgroup.orderOf_mk] at h1
  obtain ⟨⟨s₀, hs₀N⟩, hs₀, rfl⟩ := hs
  have hs₀T : s₀ ∈ S.Tv := Subgroup.mem_subgroupOf.mp hs₀
  set sS : MulAut ↥S.Uv := conjAct S.Uv ⟨s₀, hs₀N⟩ with hsS
  have hsG : sS ∈ GS := S.autOn_le_GvS S.Tv_le_Gv ⟨⟨s₀, hs₀N⟩, hs₀, rfl⟩
  have hs2 : ∃ k : ℕ, sS ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := S.isPGroup_T ⟨s₀, hs₀T.1⟩
    refine ⟨k, ?_⟩
    have : (⟨s₀, hs₀N⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [hsS, ← map_pow, this, map_one]
  obtain ⟨hconj, hcube⟩ := four_aut hU₁ (fun e _ => hsq e) hlU₁ hsU₁ hlSodd hs2 hlU hsU
  have hs₀Lv : s₀⁻¹ * l₀ * s₀ ∈ S.Lv := by
    have := (Subgroup.mem_normalizer_iff.mp (S.Tv_le_normalizer_Lv (S.Tv.inv_mem hs₀T))
      l₀).mp hl₀Lv
    simpa using this
  have hN' : s₀⁻¹ * l₀ * s₀ ∈ Subgroup.normalizer (S.Uv : Set G) :=
    S.Gv_le_normalizer_Uv (S.Lv_le_Gv hs₀Lv)
  have hconjS : sS⁻¹ * lS * sS = conjAct S.Uv ⟨s₀⁻¹ * l₀ * s₀, hN'⟩ := by
    rw [hsS, hlS, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hll : ∀ u, lS⁻¹ (lS u) = u := fun u => by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hsinv : ∀ w ∈ W, sS⁻¹ w = w := fun w hw => by
    conv_lhs => rw [← hsW w hw]
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hdW : ∀ w ∈ W, (lS⁻¹ * (sS⁻¹ * lS * sS)) w = w := by
    intro w hw
    simp only [MulAut.mul_apply]
    rw [hsW w hw, hsinv _ (hlW _ hw), hll]
  have hdU : ∀ e ∈ U₁, (lS⁻¹ * (sS⁻¹ * lS * sS)) e = lS e := by
    intro e he
    simp only [MulAut.mul_apply]
    rw [show sS⁻¹ (lS (sS e)) = lS⁻¹ e from hconj e he]
    have h3 := hcube e he
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply] at h3
    calc lS⁻¹ (lS⁻¹ e) = lS⁻¹ (lS⁻¹ (lS (lS (lS e)))) := by rw [h3]
      _ = lS e := by rw [hll, hll]
  refine ⟨lS⁻¹ * (sS⁻¹ * lS * sS), ?_, hdW, hdU, ?_, ?_⟩
  · refine Subgroup.mul_mem _ (Subgroup.inv_mem _ hlSL) ?_
    rw [hconjS]
    exact ⟨⟨_, hN'⟩, Subgroup.mem_subgroupOf.mpr hs₀Lv, rfl⟩
  · ext u
    obtain ⟨a, ha, w, hw, rfl⟩ := hdec u
    set d := lS⁻¹ * (sS⁻¹ * lS * sS)
    have e3 : (d ^ 3) (a * w) = d (d (d (a * w))) := by
      rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply]
    rw [e3, MulAut.one_apply]
    simp only [map_mul, hdW w hw]
    rw [hdU a ha, hdU _ (hlU₁ _ ha), hdU _ (hlU₁ _ (hlU₁ _ ha))]
    have h3 := hcube a ha
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply] at h3
    rw [h3]
  · intro h
    obtain ⟨e₀, he₀, hle₀⟩ := hlU
    apply hle₀
    rw [← hdU e₀ he₀, h, MulAut.one_apply]

theorem le_normalizer_Vv_of_d {U₁ W : Subgroup ↥S.Uv} (hU₁ : Nat.card U₁ = 4)
    (hdec : ∀ u : ↥S.Uv, ∃ a ∈ U₁, ∃ w ∈ W, u = a * w)
    (hGU : ∀ g ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv, ∀ u ∈ U₁, g u ∈ U₁)
    {ld : G} (hldLv : ld ∈ S.Lv) (hldV : ld ∈ Subgroup.normalizer (V : Set G))
    (hldN : ld ∈ Subgroup.normalizer (S.Uv : Set G))
    (hρ : S.frame.ρ ⟨ld, hldV⟩ = c234 ∨ S.frame.ρ ⟨ld, hldV⟩ = c234⁻¹)
    (hdW : ∀ w ∈ W, conjAct S.Uv ⟨ld, hldN⟩ w = w) :
    Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G) := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  set d : MulAut ↥S.Uv := conjAct S.Uv ⟨ld, hldN⟩ with hd
  set c := S.frame.ρ ⟨ld, hldV⟩ with hc
  have hcmem : c ∈ [c234, c234⁻¹] := by
    rcases hρ with h | h <;> simp [h]
  have hdG : d ∈ autOn Gv S.Uv :=
    S.autOn_le_GvS S.Lv_le_Gv ⟨⟨ld, hldN⟩, Subgroup.mem_subgroupOf.mpr hldLv, rfl⟩
  have hcommU : ∀ y ∈ S.Vv, ∀ hy : ld * y * ld⁻¹ * y⁻¹ ∈ S.Uv,
      (⟨ld * y * ld⁻¹ * y⁻¹, hy⟩ : ↥S.Uv) ∈ U₁ := by
    intro y hyV hy
    have hyU : y ∈ S.Uv := S.Vv_le_Uv hyV
    have e : (⟨ld * y * ld⁻¹ * y⁻¹, hy⟩ : ↥S.Uv) = d ⟨y, hyU⟩ * (⟨y, hyU⟩ : ↥S.Uv)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hd, coe_conjAct_apply']
      rfl
    rw [e]
    obtain ⟨a, ha, w, hw, hyaw⟩ := hdec ⟨y, hyU⟩
    rw [hyaw, map_mul, hdW w hw, mul_inv_rev]
    have e2 : d a * w * (w⁻¹ * a⁻¹) = d a * a⁻¹ := by group
    rw [e2]
    exact U₁.mul_mem (hGU _ hdG _ ha) (U₁.inv_mem ha)
  have hpsiC : ∀ (y : ↥V) (hk : ld * (y : G) * ld⁻¹ * (y : G)⁻¹ ∈ V),
      S.frame.ψ ⟨_, hk⟩ = pact c (S.frame.ψ y) * (S.frame.ψ y)⁻¹ := by
    intro y hk
    have hm : ld * (y : G) * ld⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hldV _).mp y.2
    have e : (⟨_, hk⟩ : ↥V) = ⟨_, hm⟩ * y⁻¹ := rfl
    rw [e, map_mul, map_inv, hc, ← S.psi_conj ⟨ld, hldV⟩ y]
  have hldv : ld ∈ Gv := S.Lv_le_Gv hldLv
  have hkVv : ∀ y ∈ S.Vv, ld * y * ld⁻¹ * y⁻¹ ∈ S.Vv := fun y hy =>
    S.Vv.mul_mem (S.conj_mem_Vv hldV hldv hy) (S.Vv.inv_mem hy)
  have hU₁Vv : ∀ u ∈ U₁, (u : G) ∈ S.Vv := by
    have hmk : ∀ t ∈ [1, E23, E24, E34], ∃ k : ↥S.Uv, k ∈ U₁ ∧ (k : G) ∈ S.Vv ∧
        ∃ hkV : (k : G) ∈ V, S.frame.ψ ⟨k, hkV⟩ = t := by
      intro t ht
      obtain ⟨y, hy, hyt⟩ := comm_c234_surj c hcmem t ht
      set y' : ↥V := S.frame.ψ.symm y with hy'
      have hy'Vv : (y' : G) ∈ S.Vv :=
        S.mem_Vv.2 ⟨y'.2, by rw [hy', MulEquiv.apply_symm_apply]; exact hy⟩
      have hkV : ld * (y' : G) * ld⁻¹ * (y' : G)⁻¹ ∈ V := S.Vv_le_V (hkVv _ hy'Vv)
      refine ⟨⟨_, S.Vv_le_Uv (hkVv _ hy'Vv)⟩, hcommU _ hy'Vv _, hkVv _ hy'Vv, hkV, ?_⟩
      rw [hpsiC y' hkV, hy', MulEquiv.apply_symm_apply, hyt]
    obtain ⟨k₁, hk₁, hk₁V, hk₁V', hk₁t⟩ := hmk 1 (by simp)
    obtain ⟨k₂, hk₂, hk₂V, hk₂V', hk₂t⟩ := hmk E23 (by simp)
    obtain ⟨k₃, hk₃, hk₃V, hk₃V', hk₃t⟩ := hmk E24 (by simp)
    obtain ⟨k₄, hk₄, hk₄V, hk₄V', hk₄t⟩ := hmk E34 (by simp)
    obtain ⟨f12, f13, f14, f23, f24, f34⟩ := E23_facts
    have hne : ∀ {k k' : ↥S.Uv} (hk : (k : G) ∈ V) (hk' : (k' : G) ∈ V) {t t' : W5},
        S.frame.ψ ⟨k, hk⟩ = t → S.frame.ψ ⟨k', hk'⟩ = t' → t ≠ t' → k ≠ k' := by
      intro k k' hk hk' t t' h h' htt' hkk'
      apply htt'
      rw [← h, ← h']
      congr 2
      exact congrArg Subtype.val hkk'
    intro u hu
    rcases eq_of_card_four hU₁ hk₁ hk₂ hk₃ hk₄ (hne _ _ hk₁t hk₂t f12) (hne _ _ hk₁t hk₃t f13)
      (hne _ _ hk₁t hk₄t f14) (hne _ _ hk₂t hk₃t f23) (hne _ _ hk₂t hk₄t f24)
      (hne _ _ hk₃t hk₄t f34) hu with rfl | rfl | rfl | rfl
    · exact hk₁V
    · exact hk₂V
    · exact hk₃V
    · exact hk₄V
  have hv12 : S.v12 ∈ S.Vv := S.mem_Vv.2 ⟨S.v12_mem_V, by rw [S.psi_v12]; decide +kernel⟩
  have key : ∀ g ∈ Gv, ∀ x ∈ S.Vv, g * x * g⁻¹ ∈ S.Vv := by
    intro g hg x hx
    obtain ⟨hxV, hc01⟩ := S.mem_Vv.1 hx
    obtain ⟨y, hy, hxy⟩ := c01_ker_comm_c234 c hcmem _ hc01
    set y' : ↥V := S.frame.ψ.symm y with hy'
    have hy'Vv : (y' : G) ∈ S.Vv :=
      S.mem_Vv.2 ⟨y'.2, by rw [hy', MulEquiv.apply_symm_apply]; exact hy⟩
    set k := ld * (y' : G) * ld⁻¹ * (y' : G)⁻¹ with hk
    have hkV : k ∈ V := S.Vv_le_V (hkVv _ hy'Vv)
    have hkUv : k ∈ S.Uv := S.Vv_le_Uv (hkVv _ hy'Vv)
    have hψk : S.frame.ψ ⟨k, hkV⟩ = pact c y * y⁻¹ := by
      rw [hpsiC y' hkV, hy', MulEquiv.apply_symm_apply]
    have hgN := S.Gv_le_normalizer_Uv hg
    have hgk : g * k * g⁻¹ ∈ S.Vv := by
      have h1 : conjAct S.Uv ⟨g, hgN⟩ ⟨k, hkUv⟩ ∈ U₁ :=
        hGU _ ⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩ _ (hcommU _ hy'Vv hkUv)
      have h2 := hU₁Vv _ h1
      rwa [coe_conjAct_apply'] at h2
    rcases hxy with h | h
    · have hxk : x = k := congrArg Subtype.val (S.frame.ψ.injective (h.trans hψk.symm))
      rw [hxk]
      exact hgk
    · have hvk : S.v12 * k ∈ V := V.mul_mem S.v12_mem_V hkV
      have e : S.frame.ψ ⟨S.v12 * k, hvk⟩ = E12 * (pact c y * y⁻¹) := by
        have e' : (⟨S.v12 * k, hvk⟩ : ↥V) = ⟨S.v12, S.v12_mem_V⟩ * ⟨k, hkV⟩ := rfl
        rw [e', map_mul, S.psi_v12, hψk]
      have hxk : x = S.v12 * k := congrArg Subtype.val (S.frame.ψ.injective (h.trans e.symm))
      rw [hxk]
      have hgv : g * S.v12 * g⁻¹ = S.v12 := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
      have e2 : g * (S.v12 * k) * g⁻¹ = (g * S.v12 * g⁻¹) * (g * k * g⁻¹) := by group
      rw [e2, hgv]
      exact S.Vv.mul_mem hv12 hgk
  intro g hg
  refine B6.mem_normalizer_of_forall_mem (key g hg) fun x hx => ?_
  have := key g⁻¹ (Gv.inv_mem hg) x hx
  simpa using this

theorem le_normalizer_Vv_of_three (hUe : IsElemAbelian 2 S.Uv)
    {Y : Subgroup (MulAut ↥S.Uv)}
    (hYG : Y ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)
    (hYn : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (Y : Set (MulAut ↥S.Uv)))
    (hY1 : Y ≠ ⊥) {U₁ W : Subgroup ↥S.Uv} (hU₁ : Nat.card U₁ = 4)
    (hdec : ∀ u : ↥S.Uv, ∃ a ∈ U₁, ∃ w ∈ W, u = a * w) (hU₁W : U₁ ⊓ W = ⊥)
    (hYW : ∀ y ∈ Y, ∀ w ∈ W, y w = w) (hYU : ∀ u ∈ U₁, (∀ y ∈ Y, y u = u) → u = 1)
    (hGU : ∀ g ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv, ∀ u ∈ U₁, g u ∈ U₁)
    (hGW : ∀ g ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv, ∀ w ∈ W, g w ∈ W)
    {s : MulAut ↥S.Uv} (hs : s ∈ autOn S.Tv S.Uv) (hsW : ∀ w ∈ W, s w = w)
    (hsU : ∃ u ∈ U₁, s u ≠ u) :
    Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G) := by
  obtain ⟨l₀, hl₀Lv, hl₀odd, hl₀σ⟩ := S.exists_Lv_c234_odd
  have hl₀N : (l₀ : G) ∈ Subgroup.normalizer (S.Uv : Set G) :=
    S.Gv_le_normalizer_Uv (S.Lv_le_Gv hl₀Lv)
  have hlU := S.exists_moved_U₁ hUe hYG hYn hY1 hdec hU₁W hYW hYU hGU hGW l₀ hl₀Lv hl₀σ hl₀N
  have hl₀G : conjAct S.Uv ⟨l₀, hl₀N⟩ ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv :=
    S.autOn_le_GvS S.Lv_le_Gv ⟨⟨l₀, hl₀N⟩, Subgroup.mem_subgroupOf.mpr hl₀Lv, rfl⟩
  have hsG : s ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv :=
    S.autOn_le_GvS S.Tv_le_Gv hs
  obtain ⟨d, hdL, hdW, hdU, hd3, hd1⟩ :=
    S.exists_d_of_three hUe hU₁ hdec l₀ hl₀Lv hl₀odd hl₀N (hGU _ hl₀G) (hGW _ hl₀G) hlU hs
      (hGU _ hsG) hsW hsU
  obtain ⟨⟨ld, hldN⟩, hldL, hdld⟩ := hdL
  have hldLv : ld ∈ S.Lv := Subgroup.mem_subgroupOf.mp hldL
  have hldV : ld ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (oTwoRes_le _ hldLv).1
  have hρ : S.frame.ρ ⟨ld, hldV⟩ = c234 ∨ S.frame.ρ ⟨ld, hldV⟩ = c234⁻¹ := by
    rcases S.rho_Lv_cases ⟨ld, hldV⟩ hldLv with h | h | h
    · exfalso
      obtain ⟨k, hk⟩ := S.two_pow_of_Lv_of_rho ⟨ld, hldV⟩ hldLv h
      have hdk : d ^ 2 ^ k = 1 := by
        rw [← hdld, ← map_pow]
        have : (⟨ld, hldN⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) ^ 2 ^ k = 1 :=
          Subtype.ext (by simpa using hk)
        rw [this, map_one]
      apply hd1
      have h1 : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
      have h2 : orderOf d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hdk
      have h3 : orderOf d ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
      have hg : Nat.gcd 3 (2 ^ k) = 1 :=
        Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
      rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact h3
    · exact Or.inl h
    · exact Or.inr h
  exact S.le_normalizer_Vv_of_d hU₁ hdec hGU hldLv hldV hldN hρ (by rw [hdld]; exact hdW)

end Setting

end CFSG.Quasithin.H13.A5
