module

public import CFSG.Quasithin.H13.A6S13821zc
public import CFSG.Quasithin.H13.A6S13821zv
public import CFSG.Quasithin.Vol2.Ch10SecQ6WrS5

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.E1.LiftS5 CFSG.Quasithin.Vol2.Ch10.SecD.C10P06

attribute [local instance] commGroupOfFact

namespace A6S20

theorem not_quad_pair : ∀ γ₁ γ₂ : Perm (Fin 5), Perm.sign γ₁ = 1 → Perm.sign γ₂ = 1 →
    γ₁ ≠ 1 → γ₂ ≠ 1 → γ₁ ≠ γ₂ → ∃ u : Fin 5 → ZMod 2, Vol2.Ch10.SecD.C10P06.IsO u ∧
      (Vol2.Ch10.SecD.C10P06.pv γ₂ (Vol2.Ch10.SecD.C10P06.pv γ₁ u + u) ≠
          Vol2.Ch10.SecD.C10P06.pv γ₁ u + u ∨
        Vol2.Ch10.SecD.C10P06.pv γ₁ (Vol2.Ch10.SecD.C10P06.pv γ₁ u + u) ≠
          Vol2.Ch10.SecD.C10P06.pv γ₁ u + u) := by
  decide +kernel

theorem exists_three_fix : ∀ p : Fin 5, ∃ σ : Perm (Fin 5), σ p = p ∧ Perm.sign σ = 1 ∧
    σ ^ 3 = 1 ∧ σ ≠ 1 := by
  decide +kernel

theorem false_of_transv_comm {W : Type*} [CommGroup W] {t α : MulAut W} {w : W}
    (ht1 : t ≠ 1) (ht : ∀ v, t v = v ∨ t v = v * w) (hαt : α * t = t * α)
    (hfpf : ∀ v, α v = v → v = 1) : False := by
  obtain ⟨v, hv⟩ : ∃ v, t v ≠ v := by
    by_contra h
    push Not at h
    exact ht1 (MulEquiv.ext h)
  have hw : t v = v * w := (ht v).resolve_left hv
  have h1 : t (α v) = α v * α w := by
    have h2 := congrArg (fun f : MulAut W => f v) hαt
    simp only [MulAut.mul_apply] at h2
    rw [← h2, hw, map_mul]
  rcases ht (α v) with h | h
  · rw [h1] at h
    have h2 : α w = 1 := by
      have h3 := congrArg (fun z => (α v)⁻¹ * z) h
      simpa using h3
    have hw1 : w = 1 := α.injective (by rw [h2, map_one])
    apply hv
    rw [hw, hw1, mul_one]
  · rw [h1] at h
    have hw1 := hfpf w (mul_left_cancel h)
    apply hv
    rw [hw, hw1, mul_one]

theorem exists_two_cosets {G : Type*} [Group G] {Y Q : Subgroup G}
    (h : 3 ≤ (Y ⊓ Q).relIndex Y) :
    ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, y₁ ∉ Q ∧ y₂ ∉ Q ∧ y₁⁻¹ * y₂ ∉ Q := by
  classical
  set N := (Y ⊓ Q).subgroupOf Y with hN
  have hidx : 3 ≤ N.index := h
  have hfin : Finite (↥Y ⧸ N) := Nat.finite_of_card_ne_zero (show N.index ≠ 0 by omega)
  have := Fintype.ofFinite (↥Y ⧸ N)
  have h2 : 2 < Fintype.card (↥Y ⧸ N) := by
    rw [← Nat.card_eq_fintype_card]
    exact (show 2 < N.index by omega)
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h2
  set o : ↥Y ⧸ N := QuotientGroup.mk 1 with ho
  obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : ↥Y ⧸ N, x ≠ o ∧ y ≠ o ∧ x ≠ y := by
    by_cases ha : a = o
    · exact ⟨b, c, fun h => hab (ha.trans h.symm), fun h => hac (ha.trans h.symm), hbc⟩
    · by_cases hb : b = o
      · exact ⟨a, c, ha, fun h => hbc (hb.trans h.symm), hac⟩
      · exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y₂, rfl⟩ := QuotientGroup.mk_surjective y
  have hnot : ∀ z : ↥Y, (QuotientGroup.mk z : ↥Y ⧸ N) ≠ o → (z : G) ∉ Q := by
    intro z hz hzQ
    apply hz
    rw [ho, QuotientGroup.eq, hN, Subgroup.mem_subgroupOf]
    exact ⟨(z⁻¹ * 1 : ↥Y).2, by simpa using hzQ⟩
  refine ⟨y₁, y₁.2, y₂, y₂.2, hnot y₁ hx, hnot y₂ hy, fun h12 => hxy ?_⟩
  rw [QuotientGroup.eq, hN, Subgroup.mem_subgroupOf]
  exact ⟨(y₁⁻¹ * y₂).2, by simpa using h12⟩

end A6S20

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_V3_not_V1 (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) :
    ∃ u ∈ S.V3, u ∉ fsuV1 T V := by
  by_contra hall
  push Not at hall
  have hF := (hS.hF H hH).toHypF91
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hF.H_normalizes_V₁
  have h4 := S.card_tilde_V3 hS hH
  have hbot : subM (fsuV1 T V) (conjClosure S.V3 H) S.V3 = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨a, haU, haw⟩ := exists_mk_of_mem_tilde w
    have hwa : w = modMk hIHN (a : G) haU := Subtype.ext haw.symm
    have haV : (a : G) ∈ S.V3 := by
      have h1 : (w : SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) ∈
          tildeOf (fsuV1 T V) S.V3 := hw
      rw [← haw] at h1
      exact (secMk_mem_tildeOf_iff hF.V₁_le_Vp).mp h1
    rw [Subgroup.mem_bot, hwa]
    exact (A6Tv.modMk_eq_one_iff' hIHN haU).mpr (hall _ haV)
  rw [hbot, Subgroup.card_bot] at h4
  norm_num at h4

theorem not_mem_QH_of_fpf (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {c : G}
    (hfpf : ∀ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V → u ∈ fsuV1 T V) :
    c ∉ pCoreOf 2 H := by
  intro hcQ
  have hF := (hS.hF H hH).toHypF91
  obtain ⟨u, hu, hu1⟩ := S.exists_V3_not_V1 hS hH
  rw [hF.pCoreOf_eq_centralizerMod] at hcQ
  exact hu1 (hfpf u (le_conjClosure S.V3 H hu) (hcQ.2.2 u (le_conjClosure S.V3 H hu)))

theorem not_mem_centralizer_of_fpf (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {c : G}
    (hfpf : ∀ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V → u ∈ fsuV1 T V) :
    c ∉ Subgroup.centralizer (V : Set G) := by
  intro hcV
  obtain ⟨u, hu, hu1⟩ := S.exists_V3_not_V1 hS hH
  have h1 : c * u * c⁻¹ * u⁻¹ = 1 := by
    rw [← Subgroup.mem_centralizer_iff.mp hcV u (S.V3_le_V hu)]
    group
  exact hu1 (hfpf u (le_conjClosure S.V3 H hu) (h1 ▸ (fsuV1 T V).one_mem))

theorem comm_c_of_mem_R (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) {c : G}
    (hcX : c ∈ S.X13820) (hc3 : c ^ 3 = 1)
    (hfpf : ∀ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V → u ∈ fsuV1 T V)
    (hdich : ∀ h ∈ H, h * c * h⁻¹ * c⁻¹ ∈ pCoreOf 2 H ∨ h * c * h⁻¹ * c ∈ pCoreOf 2 H)
    {b : G} (hb : b ∈ pCoreOf 2 (S.L1 ⊔ T)) : c * b * c⁻¹ * b⁻¹ ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := (hS.hF H hH).toHypF91
  have hLTH : S.L1 ⊔ T ≤ H := hF.L₁T_le_H
  have hcL : c ∈ S.L1 ⊔ T := Subgroup.mem_sup_left (S.plusData_X13820.le_L1 hcX)
  have hbH : b ∈ H := hLTH (pCoreOf_le 2 _ hb)
  have hQR : pCoreOf 2 H ≤ pCoreOf 2 (S.L1 ⊔ T) := by
    exact le_pCoreOf_of_le_normalizer 2
      ((F7.isSylowTwoOf_pCoreOf_le hF.sylow_H).trans le_sup_right)
      (hLTH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  rcases hdich b hbH with h | h
  · have h1 := (pCoreOf 2 H).inv_mem h
    have e : (b * c * b⁻¹ * c⁻¹)⁻¹ = c * b * c⁻¹ * b⁻¹ := by group
    rwa [e] at h1
  · exfalso
    have hcb : c * b⁻¹ * c⁻¹ ∈ pCoreOf 2 (S.L1 ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (S.L1 ⊔ T) hcL) _).mp
        ((pCoreOf 2 _).inv_mem hb)
    have h2 : b * (c * b⁻¹ * c⁻¹) ∈ pCoreOf 2 (S.L1 ⊔ T) := (pCoreOf 2 _).mul_mem hb hcb
    have h3 := (pCoreOf 2 (S.L1 ⊔ T)).mul_mem ((pCoreOf 2 _).inv_mem (hQR h)) h2
    have e : (b * c * b⁻¹ * c)⁻¹ * (b * (c * b⁻¹ * c⁻¹)) = c⁻¹ ^ 2 := by group
    rw [e] at h3
    have hc' : c⁻¹ ^ 2 = c := by
      calc c⁻¹ ^ 2 = c⁻¹ ^ 2 * c ^ 3 := by rw [hc3, mul_one]
        _ = c := by group
    rw [hc'] at h3
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (S.L1 ⊔ T) ⟨c, h3⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h4 : orderOf c ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one hk')
    have h5 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
    rw [h5, Nat.dvd_one, orderOf_eq_one_iff] at h4
    exact S.not_mem_QH_of_fpf hS hH hfpf (h4 ▸ (pCoreOf 2 H).one_mem)

theorem not_transv_of_comm (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {c : G}
    (hcH : c ∈ H)
    (hfpf : ∀ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V → u ∈ fsuV1 T V)
    {x : G} (hxH : x ∈ H) (hxc : x * c * x⁻¹ * c⁻¹ ∈ pCoreOf 2 H) :
    ¬ InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V) := by
  intro htr
  have hF := (hS.hF H hH).toHypF91
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF.isElemAbelian_tilde⟩
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  obtain ⟨ht1, w, -, hw⟩ := A6Tv.isTransvection_actH hV₁ hIHN hIH hxH htr
  have hcomm : actH hV₁ hIH ⟨c, hcH⟩ * actH hV₁ hIH ⟨x, hxH⟩ =
      actH hV₁ hIH ⟨x, hxH⟩ * actH hV₁ hIH ⟨c, hcH⟩ := by
    have hq : (⟨x, hxH⟩ * ⟨c, hcH⟩ * (⟨x, hxH⟩ : ↥H)⁻¹ * (⟨c, hcH⟩ : ↥H)⁻¹ : ↥H) ∈
        (actH hV₁ hIH).ker := by
      rw [MonoidHom.mem_ker, A6Tv.actH_eq_one_iff hV₁ hIHN hIH]
      have h1 := hxc
      rw [hF.pCoreOf_eq_centralizerMod] at h1
      exact h1.2.2
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hq
    have h2 := mul_inv_eq_one.mp hq
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  refine A6S20.false_of_transv_comm ht1 hw hcomm fun v hv => ?_
  obtain ⟨a, haU, haw⟩ := exists_mk_of_mem_tilde v
  have hv' : v = modMk hIHN (a : G) haU := Subtype.ext haw.symm
  subst hv'
  rw [actH_modMk hV₁ hIHN hIH ⟨c, hcH⟩ haU] at hv
  have h1 := (A6Tv.modMk_conj_eq_iff' hIHN haU _).mp hv
  exact (A6Tv.modMk_eq_one_iff' hIHN haU).mpr (hfpf _ haU h1)

theorem mem_QH_of_mem_R (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHK : H = K ⊔ (S.L1 ⊔ T))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) {r : G}
    (hrR : r ∈ pCoreOf 2 (S.L1 ⊔ T)) (hrH : r ∈ H) (hr : quotPerm hKn e ⟨r, hrH⟩ = 1) :
    r ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := (hS.hF H hH).toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hLTH : S.L1 ⊔ T ≤ H := hF.L₁T_le_H
  set R := pCoreOf 2 (S.L1 ⊔ T) with hR
  have hQR : pCoreOf 2 H ≤ R := by
    exact le_pCoreOf_of_le_normalizer 2
      ((F7.isSylowTwoOf_pCoreOf_le hF.sylow_H).trans le_sup_right)
      (hLTH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
  set N : Subgroup G := R ⊓ ((quotPerm hKn e).ker.map H.subtype) with hN
  have hmemN : ∀ {x : G} (hx : x ∈ H), x ∈ R → quotPerm hKn e ⟨x, hx⟩ = 1 → x ∈ N :=
    fun hx hxR hx1 => ⟨hxR, ⟨⟨_, hx⟩, MonoidHom.mem_ker.mpr hx1, rfl⟩⟩
  have hNH : N ≤ H := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx.2
    exact y.2
  have hψN : ∀ {x : G} (hx : x ∈ N), quotPerm hKn e ⟨x, hNH hx⟩ = 1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hx.2
    have e' : (⟨x, hNH hx⟩ : ↥H) = y := Subtype.ext hyx.symm
    rw [e']
    exact MonoidHom.mem_ker.mp hy
  have hconj : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ R → g * x * g⁻¹ ∈ N := by
    intro g hg x hx hgx
    have hgxH : g * x * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg (hNH hx)) (H.inv_mem hg)
    refine hmemN hgxH hgx ?_
    have e' : (⟨g * x * g⁻¹, hgxH⟩ : ↥H) = ⟨g, hg⟩ * ⟨x, hNH hx⟩ * (⟨g, hg⟩ : ↥H)⁻¹ := rfl
    rw [e', map_mul, map_mul, map_inv, hψN hx, mul_one, mul_inv_cancel]
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := by
    have hkey : ∀ g ∈ H, (∀ x ∈ N, g * x * g⁻¹ ∈ R) → (∀ x ∈ N, g⁻¹ * x * g⁻¹⁻¹ ∈ R) →
        g ∈ Subgroup.normalizer (N : Set G) := by
      intro g hg h1 h2
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hconj g hg x hx (h1 x hx), fun hx => ?_⟩
      have h3 := hconj g⁻¹ (H.inv_mem hg) _ hx (h2 _ hx)
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h3
    have hLT : S.L1 ⊔ T ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
      hkey g (hLTH hg)
        (fun x hx => (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hg) x).mp hx.1)
        (fun x hx => (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_pCoreOf 2 _ ((S.L1 ⊔ T).inv_mem hg)) x).mp hx.1)
    have hKR : ∀ k ∈ K, ∀ x ∈ N, k * x * k⁻¹ ∈ R := by
      intro k hk x hx
      have h1 := (A6L24.quotPerm_eq_one_iff hKn e ⟨x, hNH hx⟩).mp (hψN hx) k⁻¹ (K.inv_mem hk)
      have h2 : k * (x * k⁻¹ * x⁻¹ * k⁻¹⁻¹) * k⁻¹ ∈ pCoreOf 2 K :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hk) _).mp h1
      have e' : k * x * k⁻¹ = (k * (x * k⁻¹ * x⁻¹ * k⁻¹⁻¹) * k⁻¹) * x := by group
      rw [e']
      exact R.mul_mem (hQR (hOQ h2)) hx.1
    have hK : K ≤ Subgroup.normalizer (N : Set G) := fun k hk =>
      hkey k (hKH hk) (hKR k hk) (fun x hx => hKR k⁻¹ (K.inv_mem hk) x hx)
    rw [hHK]
    exact sup_le hK hLT
  have hNp : IsPGroup 2 N := (pCoreOf_isPGroup 2 (S.L1 ⊔ T)).to_le inf_le_left
  exact le_pCoreOf_of_le_normalizer 2 hNH hHN hNp (hmemN hrH hrR hr)

theorem exists_d_13820a (h1337 : Stmt13_3_7) (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) {p₀ : Fin 5}
    (hfix : ∀ g : ↥H, quotPerm hKn e g p₀ = p₀ ↔
      (g : G) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hBM : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G))
    {c : G} (hcX : c ∈ S.X13820) (hc3 : c ^ 3 = 1) (hcV : c ∉ Subgroup.centralizer (V : Set G))
    (htri : ∀ y ∈ S.X13820, y ∈ pCoreOf 2 H ∨ y * c⁻¹ ∈ pCoreOf 2 H ∨ y * c ∈ pCoreOf 2 H)
    {s : G} (hsT : s ∈ T) (hsc : s * c * s⁻¹ * c ∈ pCoreOf 2 H)
    (hsK : ∀ k ∈ K, s * k * s⁻¹ * k⁻¹ ∈ pCoreOf 2 H) :
    ∃ d : G, ∃ hdH : d ∈ H, d ∈ S.L1 ∧ d ∈ K ∧
      d ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ∧ d ^ 3 = 1 ∧
      quotPerm hKn e ⟨d, hdH⟩ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨σ, hσp, hσs, hσ3, hσ1⟩ := A6S20.exists_three_fix p₀
  obtain ⟨k, hkK, hkσ⟩ := A6L24.exists_lift hKH hKn e (Perm.mem_alternatingGroup.mpr hσs)
  obtain ⟨a, r, hr, hkr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (k : G)).ne'
  set d : G := (k : G) ^ 2 ^ a with hd
  have hdH : d ∈ H := H.pow_mem k.2 _
  have hdK : d ∈ K := K.pow_mem hkK _
  have hdk : (⟨d, hdH⟩ : ↥H) = k ^ 2 ^ a := Subtype.ext (by simp [hd])
  have hψd : quotPerm hKn e ⟨d, hdH⟩ = σ ^ 2 ^ a := by rw [hdk, map_pow, hkσ]
  have hσ3' : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hψd1 : quotPerm hKn e ⟨d, hdH⟩ ≠ 1 := by
    rw [hψd]
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hσ3'] at h1
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h1)) (by decide)
  have hdord : orderOf d = r := by
    rw [hd, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨r, hkr⟩, hkr,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hd3 : d ^ 3 = 1 := by
    have hψ3 : quotPerm hKn e ⟨d ^ 3, H.pow_mem hdH 3⟩ = 1 := by
      have e' : (⟨d ^ 3, H.pow_mem hdH 3⟩ : ↥H) = (⟨d, hdH⟩ : ↥H) ^ 3 := Subtype.ext (by simp)
      rw [e', map_pow, hψd, ← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
    have hO := (A6L24.quotPerm_eq_one_iff_of_mem hKn e _ (K.pow_mem hdK 3)).mp hψ3
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K ⟨_, hO⟩
    have hb' : (d ^ 3) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have h1 : orderOf (d ^ 3) ∣ Nat.gcd (2 ^ b) r :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hb') (hdord ▸ orderOf_pow_dvd 3)
    have h2 : Nat.gcd (2 ^ b) r = 1 :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hr)))
    rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have hpow : ∀ m : ℕ, (σ ^ m) p₀ = p₀ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, Perm.mul_apply, hσp, ih]
  have hdN : d ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    refine (hfix ⟨d, hdH⟩).mp ?_
    rw [hψd]
    exact hpow _
  have hdM := hBM ⟨hdK, hdN⟩
  have hdC := S.mem_centralizer_of_odd_13820a hS hH hcX hc3 hcV htri hsT hsc hsK hdK hdH hdM
    (hdord ▸ hr)
  have hd1 : d ≠ 1 := fun h => hψd1 (by
    have e' : (⟨d, hdH⟩ : ↥H) = 1 := Subtype.ext h
    rw [e', map_one])
  have hdo3 : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have h3C : 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G)) := by
    have h1 := orderOf_dvd_natCard (⟨d, hdC⟩ : ↥(Subgroup.centralizer (V : Set G)))
    rwa [Subgroup.orderOf_mk, hdo3] at h1
  obtain ⟨-, -, hL0⟩ := (h1337 G T L V S.h13 S.irr S.a6).resolve_left (not_not.mpr h3C)
  have hdL0 : d ∈ l0 L := by
    rw [hL0]
    exact Subgroup.subset_closure ⟨hdC, hdo3⟩
  exact ⟨d, hdH, S.l0_le_L1 hdL0, hdK, hdN, hd3, hψd1⟩

theorem isV4_of_mem_R_13820a {H K : Subgroup G} (hLTH : S.L1 ⊔ T ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) {p₀ : Fin 5}
    (hfix : ∀ g : ↥H, (g : G) ∈ S.L1 ⊔ T → quotPerm hKn e g p₀ = p₀) {d : G} (hdH : d ∈ H)
    (hdL : d ∈ S.L1) (hd3 : d ^ 3 = 1) (hψd : quotPerm hKn e ⟨d, hdH⟩ ≠ 1) {r : G}
    (hr : r ∈ pCoreOf 2 (S.L1 ⊔ T)) :
    A6L24.IsV4 p₀ (quotPerm hKn e ⟨r, hLTH (pCoreOf_le 2 _ hr)⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (S.L1 ⊔ T) with hR
  have hdLT : d ∈ S.L1 ⊔ T := Subgroup.mem_sup_left hdL
  have hdp : quotPerm hKn e ⟨d, hdH⟩ p₀ = p₀ := hfix _ hdLT
  have hψd3 : quotPerm hKn e ⟨d, hdH⟩ ^ 3 = 1 := by
    have h1 : (⟨d, hdH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [← map_pow, h1, map_one]
  have h4 : ∀ g : ↥H, (g : G) ∈ R → quotPerm hKn e g ^ 4 = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (S.L1 ⊔ T) ⟨_, hg⟩
    exact A6L24.pow_four_eq_one hKn e (k := k) (by simpa using congrArg Subtype.val hk)
  have hRn : ∀ x ∈ R, d * x * d⁻¹ ∈ R ∧ d⁻¹ * x * d ∈ R := by
    intro x hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (S.L1 ⊔ T) hdLT) x).mp hx,
      ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (S.L1 ⊔ T) ((S.L1 ⊔ T).inv_mem hdLT)) x).mp hx
    simpa using h1
  set rr : ↥H := ⟨r, hLTH (pCoreOf_le 2 _ hr)⟩ with hrr
  set dd : ↥H := ⟨d, hdH⟩ with hdd
  have hA := h4 (rr * (dd * rr * dd⁻¹)) (R.mul_mem hr (hRn r hr).1)
  have hB := h4 (rr * (dd⁻¹ * rr * dd)) (R.mul_mem hr (hRn r hr).2)
  have hC := h4 ((dd * rr * dd⁻¹) * (dd⁻¹ * rr * dd)) (R.mul_mem (hRn r hr).1 (hRn r hr).2)
  simp only [map_mul, map_inv] at hA hB hC
  exact A6L24.isV4_of_normal p₀ _ ⟨hdp, hψd3, hψd⟩ _
    ⟨hfix rr (pCoreOf_le 2 _ hr), h4 rr hr, hA, hB, hC⟩

end Setting4

end CFSG.Quasithin.H13.A6
