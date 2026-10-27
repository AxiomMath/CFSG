module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeaves
public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoAlt
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint Subgroup

section Generic

variable {X : Type} [Group X]

theorem le_normalizer_pCoreOf (Y : Subgroup X) :
    Y ≤ Subgroup.normalizer (pCoreOf 2 Y : Set X) := by
  have key : ∀ g ∈ Y, ∀ u : X, u ∈ pCoreOf 2 Y → g * u * g⁻¹ ∈ pCoreOf 2 Y := by
    intro g hg u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    refine Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : ↥Y) * v * (⟨g, hg⟩ : ↥Y)⁻¹, ?_, ?_⟩
    · exact (CFSG.pCore_normal (p := 2) (G := ↥Y)).conj_mem v hv _
    · simp
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact key y hy u hu
  · intro hu
    have h := key y⁻¹ (Y.inv_mem hy) _ hu
    simpa [mul_assoc] using h

theorem pCoreOf_le_self (H : Subgroup X) : pCoreOf 2 H ≤ H :=
  Subgroup.map_subtype_le _

theorem le_ker_of_central {H : Type} [Group H] (θ : H →* alternatingGroup (Fin 6))
    (hθ : Function.Surjective θ) (N : Subgroup H) [hN : N.Normal]
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) : N ≤ θ.ker := by
  haveI : (N.map θ).Normal := hN.map θ hθ
  have hbot : N.map θ = ⊥ := by
    apply eq_bot_of_normal_comm_alt6 (N.map θ)
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  intro x hx
  have hmem : θ x ∈ N.map θ := Subgroup.mem_map_of_mem θ hx
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

end Generic

theorem o2_quotient_of_surj {H X : Type} [Group H] [Finite H] [Group X] (ψ : H →* X)
    (θ : H →* alternatingGroup (Fin 6)) (hθ : Function.Surjective θ) (hker : ψ.ker ≤ θ.ker)
    (h2 : IsPGroup 2 θ.ker) :
    ∃ φ : ↥ψ.range →* alternatingGroup (Fin 6), Function.Surjective φ ∧
      φ.ker = CFSG.pCore 2 ↥ψ.range ∧ ∀ h : H, φ ⟨ψ h, h, rfl⟩ = θ h := by
  let ρ := QuotientGroup.quotientKerEquivRange ψ
  let Λ : H ⧸ ψ.ker →* alternatingGroup (Fin 6) := QuotientGroup.lift ψ.ker θ hker
  let φ : ↥ψ.range →* alternatingGroup (Fin 6) := Λ.comp ρ.symm.toMonoidHom
  have hφ : ∀ h : H, φ ⟨ψ h, h, rfl⟩ = θ h := by
    intro h
    have hρ : ρ.symm ⟨ψ h, h, rfl⟩ = (QuotientGroup.mk h : H ⧸ ψ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hρ]
    exact QuotientGroup.lift_mk ψ.ker hker h
  have hsurj : Function.Surjective φ := by
    intro a
    obtain ⟨h, rfl⟩ := hθ a
    exact ⟨⟨ψ h, h, rfl⟩, hφ h⟩
  refine ⟨φ, hsurj, ?_, hφ⟩
  apply le_antisymm
  ·
    apply CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (MonoidHom.normal_ker φ)
    intro g
    obtain ⟨h, hh⟩ := g.1.2
    have hθh : θ h = 1 := by
      rw [← hφ h]
      have hg := g.2
      rw [MonoidHom.mem_ker] at hg
      have : (⟨ψ h, h, rfl⟩ : ↥ψ.range) = g.1 := Subtype.ext hh
      rw [this]
      exact hg
    obtain ⟨k, hk⟩ := h2 ⟨h, by rw [MonoidHom.mem_ker]; exact hθh⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have hk' : h ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hψ : ((g.1 : ↥ψ.range) : X) ^ 2 ^ k = 1 := by
      rw [← hh, ← map_pow, hk', map_one]
    simpa using hψ
  ·
    intro x hx
    have hN : ((CFSG.pCore 2 ↥ψ.range).map φ).Normal :=
      (CFSG.pCore_normal (p := 2) (G := ↥ψ.range)).map φ hsurj
    have hP : IsPGroup 2 ((CFSG.pCore 2 ↥ψ.range).map φ) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥ψ.range)).map φ
    haveI := hN
    have hbot := eq_bot_of_normal_isPGroup_alt6 ((CFSG.pCore 2 ↥ψ.range).map φ) hP
    have hmem : φ x ∈ (CFSG.pCore 2 ↥ψ.range).map φ := Subgroup.mem_map_of_mem φ hx
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [MonoidHom.mem_ker]
    exact hmem

section Transport

variable {G : Type} [Group G] {K : Subgroup G}

theorem commutator_subgroupOf_eq {A B : Subgroup G} (hA : A ≤ K) (hB : B ≤ K)
    (h : ⁅A, B⁆ = A) : ⁅A.subgroupOf K, B.subgroupOf K⁆ = A.subgroupOf K := by
  apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
  rw [Subgroup.map_commutator]
  simp only [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA, inf_eq_left.mpr hB]
  exact h

theorem card_map_mk_mul_card_inf [Finite G] (H : Subgroup ↥K) :
    Nat.card ↥(H.map (QuotientGroup.mk' (Subgroup.center ↥K))) *
      Nat.card ↥(H ⊓ Subgroup.center ↥K) = Nat.card ↥H := by
  let f : ↥H →* (↥K ⧸ Subgroup.center ↥K) :=
    (QuotientGroup.mk' (Subgroup.center ↥K)).comp H.subtype
  have hrange : f.range = H.map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    show ((QuotientGroup.mk' (Subgroup.center ↥K)).comp H.subtype).range = _
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  have hker : f.ker = (H ⊓ Subgroup.center ↥K).subgroupOf H := by
    ext x
    simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have h1 : Nat.card ↥H = Nat.card (↥H ⧸ f.ker) * Nat.card ↥f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (↥H ⧸ f.ker) = Nat.card ↥(H.map (QuotientGroup.mk' (Subgroup.center ↥K))) := by
    rw [← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h3 : Nat.card ↥f.ker = Nat.card ↥(H ⊓ Subgroup.center ↥K) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      H ⊓ Subgroup.center ↥K ≤ H)).toEquiv
  rw [h1, h2, h3]

theorem isElemAbelian_map_mk (H : Subgroup ↥K) (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hsq : ∀ x ∈ H, x ^ 2 = 1) :
    IsElemAbelian 2 (H.map (QuotientGroup.mk' (Subgroup.center ↥K))) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul,
      hcomm x hx y hy]
  · intro a ha
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
    rw [← hxa, ← map_pow, hsq x hx, map_one]

end Transport

structure Setup {G : Type} [Group G] (K L E : Subgroup G) : Prop where
  hLK : L ≤ K
  hperf : ⁅L, L⁆ = L
  hO2 : quasithinO2QuotientIso L ↥(alternatingGroup (Fin 6))
  hE : E ≤ pCoreOf 2 L
  hEab : IsElemAbelian 2 E
  hLN : L ≤ Subgroup.normalizer (E : Set G)
  hEcomm : ⁅E, L⁆ = E
  hEcard : Nat.card ↥E = 32
  hC : Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) = 2

namespace Setup

variable {G : Type} [Group G] [Finite G] {K L E : Subgroup G}

theorem le_K (S : Setup K L E) : E ≤ K := (S.hE.trans (pCoreOf_le_self L)).trans S.hLK

theorem config (S : Setup K L E) :
    A6Config ((L.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)))
      ((E.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) := by
  obtain ⟨φL, hφLsurj, hφLker⟩ := S.hO2
  let e : ↥(L.subgroupOf K) ≃* ↥L := Subgroup.subgroupOfEquivOfLe S.hLK
  let θ : ↥(L.subgroupOf K) →* alternatingGroup (Fin 6) := φL.comp e.toMonoidHom
  have hθsurj : Function.Surjective θ := hφLsurj.comp e.surjective
  have h2θ : IsPGroup 2 θ.ker := by
    intro g
    have hg : e (g : ↥(L.subgroupOf K)) ∈ CFSG.pCore 2 ↥L := by
      rw [← hφLker, MonoidHom.mem_ker]
      have := g.2
      rw [MonoidHom.mem_ker] at this
      exact this
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨e g, hg⟩
    refine ⟨k, Subtype.ext ?_⟩
    apply e.injective
    show e ((g : ↥(L.subgroupOf K)) ^ 2 ^ k) = e 1
    rw [map_pow, map_one]
    have hk' : (e (g : ↥(L.subgroupOf K))) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    exact hk'
  let ψ : ↥(L.subgroupOf K) →* (↥K ⧸ Subgroup.center ↥K) :=
    (QuotientGroup.mk' (Subgroup.center ↥K)).comp (L.subgroupOf K).subtype
  have hcomm : ∀ x ∈ ψ.ker, ∀ y ∈ ψ.ker, x * y = y * x := by
    intro x hx y hy
    rw [MonoidHom.mem_ker] at hx hy
    have hx' : (x : K) ∈ Subgroup.center ↥K := by
      rw [← QuotientGroup.eq_one_iff]
      exact hx
    have hy' : (y : K) ∈ Subgroup.center ↥K := by
      rw [← QuotientGroup.eq_one_iff]
      exact hy
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact ((Subgroup.mem_center_iff.mp hx' (y : K))).symm
  have hkerle : ψ.ker ≤ θ.ker := le_ker_of_central θ hθsurj ψ.ker hcomm
  obtain ⟨φY, hφYsurj, hφYker, hφYapp⟩ := o2_quotient_of_surj ψ θ hθsurj hkerle h2θ
  have hYeq : ψ.range = (L.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, commutator_subgroupOf_eq S.hLK S.hLK S.hperf]
  · rw [← hYeq]
    exact ⟨φY, hφYsurj, hφYker⟩
  ·
    rw [← hYeq]
    intro f hf
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hf
    have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
    have hxL : (x : G) ∈ L := (S.hE.trans (pCoreOf_le_self L)) hxE
    have hxL' : x ∈ L.subgroupOf K := Subgroup.mem_subgroupOf.mpr hxL
    have hθ : θ ⟨x, hxL'⟩ = 1 := by
      have hu : e ⟨x, hxL'⟩ ∈ φL.ker := by
        rw [hφLker]
        obtain ⟨u, hu, huL⟩ := Subgroup.mem_map.mp (S.hE hxE)
        have hue : e ⟨x, hxL'⟩ = u := Subtype.ext huL.symm
        rw [hue]
        exact hu
      exact (MonoidHom.mem_ker).mp hu
    have hmem : (⟨ψ ⟨x, hxL'⟩, ⟨x, hxL'⟩, rfl⟩ : ↥ψ.range) ∈ CFSG.pCore 2 ↥ψ.range := by
      rw [← hφYker, MonoidHom.mem_ker, hφYapp, hθ]
    exact Subgroup.mem_map.mpr ⟨⟨ψ ⟨x, hxL'⟩, ⟨x, hxL'⟩, rfl⟩, hmem, rfl⟩
  ·
    refine isElemAbelian_map_mk (E.subgroupOf K) ?_ ?_
    · intro x hx y hy
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
      have hyE : (y : G) ∈ E := Subgroup.mem_subgroupOf.mp hy
      have := (S.hEab.1.is_comm.comm (⟨(x : G), hxE⟩ : ↥E) ⟨(y : G), hyE⟩)
      exact congrArg Subtype.val this
    · intro x hx
      have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact S.hEab.2 (x : G) hxE
  ·
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
    have hconj : ∀ l' ∈ L.subgroupOf K,
        ∀ e ∈ (E.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)),
        QuotientGroup.mk' (Subgroup.center ↥K) l' * e *
          (QuotientGroup.mk' (Subgroup.center ↥K) l')⁻¹ ∈
          (E.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
      intro l' hl' e he
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp he
      have heq : QuotientGroup.mk' (Subgroup.center ↥K) l' *
          QuotientGroup.mk' (Subgroup.center ↥K) z *
          (QuotientGroup.mk' (Subgroup.center ↥K) l')⁻¹ =
          QuotientGroup.mk' (Subgroup.center ↥K) (l' * z * l'⁻¹) := by
        simp only [map_mul, map_inv]
      rw [heq]
      refine Subgroup.mem_map.mpr ⟨l' * z * l'⁻¹, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      have hzE : (z : G) ∈ E := Subgroup.mem_subgroupOf.mp hz
      have hc : (l' : G) * (z : G) * (l' : G)⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.mp (S.hLN (Subgroup.mem_subgroupOf.mp hl')) (z : G)).mp hzE
      simpa using hc
    intro f
    constructor
    · intro hf
      exact hconj l hl f hf
    · intro hf
      have h := hconj l⁻¹ (inv_mem hl) _ hf
      simpa [map_inv, mul_assoc] using h
  · rw [← Subgroup.map_commutator, commutator_subgroupOf_eq S.le_K S.hLK S.hEcomm]

theorem map_inf_center_le (S : Setup K L E) :
    ((E.subgroupOf K) ⊓ Subgroup.center ↥K).map K.subtype ≤ E ⊓ Subgroup.centralizer (L : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hxE, hxZ⟩ := hx
  rw [Subgroup.mem_inf]
  refine ⟨Subgroup.mem_subgroupOf.mp hxE, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hlK : l ∈ K := S.hLK hl
  have hc := Subgroup.mem_center_iff.mp hxZ ⟨l, hlK⟩
  have := congrArg Subtype.val hc
  simpa using this

theorem card_inf_center_le (S : Setup K L E) :
    Nat.card ↥((E.subgroupOf K) ⊓ Subgroup.center ↥K) ≤ 2 := by
  rw [← Subgroup.card_map_of_injective (f := K.subtype) K.subtype_injective, ← S.hC]
  exact Subgroup.card_le_of_le (S.map_inf_center_le)

theorem card_F_mul (S : Setup K L E) :
    Nat.card ↥((E.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) *
      Nat.card ↥((E.subgroupOf K) ⊓ Subgroup.center ↥K) = 32 := by
  rw [card_map_mk_mul_card_inf (E.subgroupOf K)]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.le_K).toEquiv, S.hEcard]

theorem card_F_cases (S : Setup K L E) :
    Nat.card ↥((E.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) = 16 ∨
      Nat.card ↥((E.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) = 32 := by
  have hm := S.card_F_mul
  have hk : 0 < Nat.card ↥((E.subgroupOf K) ⊓ Subgroup.center ↥K) := Nat.card_pos
  have hk2 := S.card_inf_center_le
  generalize Nat.card ↥((E.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) = m at hm ⊢
  generalize Nat.card ↥((E.subgroupOf K) ⊓ Subgroup.center ↥K) = k at hm hk hk2
  interval_cases k
  · right; omega
  · left; omega

theorem centralizer_le_center_of_card_le (S : Setup K L E)
    (h : Nat.card ↥((E.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) ≤ 16) :
    E ⊓ Subgroup.centralizer (L : Set G) ≤ (Subgroup.center ↥K).map K.subtype := by
  have hm := S.card_F_mul
  have hk : 0 < Nat.card ↥((E.subgroupOf K) ⊓ Subgroup.center ↥K) := Nat.card_pos
  have hk2 := S.card_inf_center_le
  have hk_eq : Nat.card ↥((E.subgroupOf K) ⊓ Subgroup.center ↥K) = 2 := by
    generalize Nat.card ↥((E.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) = m at hm h
    generalize Nat.card ↥((E.subgroupOf K) ⊓ Subgroup.center ↥K) = k at hm hk hk2 ⊢
    interval_cases k <;> omega
  have hmap : Nat.card ↥(((E.subgroupOf K) ⊓ Subgroup.center ↥K).map K.subtype) = 2 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hk_eq]
  have heq : ((E.subgroupOf K) ⊓ Subgroup.center ↥K).map K.subtype = E ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.eq_of_le_of_card_ge S.map_inf_center_le (by rw [hmap, S.hC])
  rw [← heq]
  exact Subgroup.map_mono inf_le_right

end Setup

theorem five_dvd_of_config {X : Type} [Group X] [Finite X] {Y F : Subgroup X}
    (hY : A6Config Y F) (h16 : 16 ∣ Nat.card ↥F) : 5760 ∣ Nat.card X := by
  obtain ⟨-, ⟨φ, hφs, hφk⟩, hFY, -, -, -⟩ := hY
  have h1 : Nat.card ↥Y = Nat.card (↥Y ⧸ φ.ker) * Nat.card ↥φ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 : Nat.card (↥Y ⧸ φ.ker) = 360 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv, card_alt6]
  have h3 : Nat.card ↥φ.ker = Nat.card ↥(pCoreOf 2 Y) := by
    rw [hφk]
    exact (Subgroup.card_map_of_injective (f := Y.subtype) Y.subtype_injective).symm
  have h4 : 16 ∣ Nat.card ↥(pCoreOf 2 Y) :=
    h16.trans (Subgroup.card_dvd_of_le hFY)
  have h5 : 5760 ∣ Nat.card ↥Y := by
    rw [h1, h2, h3]
    have := Nat.mul_dvd_mul_left 360 h4
    norm_num at this ⊢
    exact this
  exact h5.trans (Subgroup.card_subgroup_dvd_card Y)

theorem comm_of_isElemAbelian {X : Type} [Group X] {F : Subgroup X} (hF : IsElemAbelian 2 F)
    {a b : X} (ha : a ∈ F) (hb : b ∈ F) : a * b = b * a :=
  congrArg Subtype.val (hF.1.is_comm.comm (⟨a, ha⟩ : ↥F) ⟨b, hb⟩)

theorem four_le_twoRank_of_config {X : Type} [Group X] [Finite X] {F : Subgroup X}
    (hF : IsElemAbelian 2 F) (h16 : 16 ≤ Nat.card ↥F) : 4 ≤ CFSG.Open.twoRank X := by
  have hP : IsPGroup 2 ↥F := fun g => ⟨1, Subtype.ext (by simpa using hF.2 g.1 g.2)⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn4 : 4 ≤ n := by
    by_contra hlt
    have : 2 ^ n < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 2 ^ 4 ∣ Nat.card ↥F := by
    rw [hn]
    exact pow_dvd_pow 2 hn4
  obtain ⟨K', hK'card, -⟩ := Sylow.exists_subgroup_card_pow_prime_le (G := ↥F) 2 (n := 0)
    (m := 4) hdvd (⊥ : Subgroup ↥F) (by simp) (by norm_num)
  let E' : Subgroup X := K'.map F.subtype
  have hE'card : Nat.card ↥E' = 2 ^ 4 := by
    rw [Subgroup.card_map_of_injective F.subtype_injective, hK'card]
  have hE'le : E' ≤ F := Subgroup.map_subtype_le K'
  have hE' : IsElemAbelian 2 E' := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb]
      exact comm_of_isElemAbelian hF (hE'le (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
        (hE'le (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩))
    · intro a ha
      exact (show a ^ 2 = 1 from by
        have := hF.2 a (hE'le ha)
        exact this)
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup X, E ≤ ⊤ ∧ IsElemAbelian 2 E ∧
      Nat.card ↥E = 2 ^ k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro k ⟨E, -, -, hEk⟩
    have hdvd' : Nat.card ↥E ∣ Nat.card X := Subgroup.card_subgroup_dvd_card E
    have hle : 2 ^ k ≤ Nat.card X := by
      rw [← hEk]
      exact Nat.le_of_dvd Nat.card_pos hdvd'
    exact (Nat.lt_two_pow_self).le.trans hle
  show 4 ≤ sSup {k : ℕ | ∃ E : Subgroup X, E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card ↥E = 2 ^ k}
  exact le_csSup hbdd ⟨E', le_top, hE', hE'card⟩


end CFSG.Quasithin.H13.K1262Two
