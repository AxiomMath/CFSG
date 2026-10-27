module

public import CFSG.Quasithin.H13.A6S1372L76Z
public import CFSG.Quasithin.H13.A6S1372L76W
public import CFSG.Quasithin.H13.A6S1372L76P4b
public import CFSG.Quasithin.Background.SQTKQuotTwo
public import CFSG.Quasithin.EmptyFaithful.R3c2Types
public import CFSG.Quasithin.Background.F918P4
public import CFSG.Quasithin.Vol2.Ch10SecV1SK
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.Quasithin.Vol2.Ch11SecAKE14
public import CFSG.Quasithin.H13.A6S1372L76M

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76Z

variable {F : Type} [Field F]

@[expose] noncomputable def scal3 (ω : Fˣ) (h3 : ω ^ 3 = 1) :
    ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
  A6L76M.slOf (Matrix.diagonal fun _ => (ω : F)) (by
    rw [Matrix.det_diagonal, Fin.prod_univ_three, ← pow_two, ← pow_succ,
      ← Units.val_pow_eq_pow_val, h3, Units.val_one])

theorem scal3_val (ω : Fˣ) (h3 : ω ^ 3 = 1) :
    (((scal3 ω h3 : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal fun _ => (ω : F) := rfl

theorem scal3_comm (ω : Fˣ) (h3 : ω ^ 3 = 1) (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) :
    scal3 ω h3 * γ = γ * scal3 ω h3 := by
  apply Subtype.ext
  apply Units.ext
  show (Matrix.diagonal fun _ => (ω : F)) * (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
    (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) * Matrix.diagonal fun _ => (ω : F)
  rw [← Matrix.scalar_apply]
  exact (Matrix.scalar_commute (ω : F) (fun r => Commute.all _ r) _).eq

theorem scal3_pow_three (ω : Fˣ) (h3 : ω ^ 3 = 1) : scal3 ω h3 ^ 3 = 1 := by
  refine A6L76M.ext_val fun v => ?_
  funext i
  rw [pow_three, A6L76M.val_mul, A6L76M.val_mul, scal3_val, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec_diagonal, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]
  rw [← mul_assoc, ← mul_assoc, ← pow_two, ← pow_succ, ← Units.val_pow_eq_pow_val, h3,
    Units.val_one, one_mul]

theorem scal3_ne_one (ω : Fˣ) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) : scal3 ω h3 ≠ 1 := by
  intro h
  have h2 := congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) =>
    (((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) 0 0) h
  simp only [scal3_val, Matrix.diagonal_apply_eq, OneMemClass.coe_one, Units.val_one,
    Matrix.one_apply_eq] at h2
  exact h1 (Units.ext h2)

theorem natRealizes_clean {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)} {U Z : Subgroup W}
    {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) →* ↥Y}
    (h : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).RealizesVia Y U Z π) :
    Function.Surjective π ∧ (∀ y : ↥Y, ∀ u ∈ U, (y : MulAut W) u ∈ U) ∧
      ∃ β : ↥U →* Multiplicative (Fin 3 → F), Function.Surjective β ∧
        (∀ u, β u = 1 ↔ (u : W) ∈ Z) ∧
        ∀ (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (u : ↥U)
          (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ U),
          β ⟨_, hu⟩ = Multiplicative.ofAdd ((((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ
            Multiplicative.toAdd (β u)) := by
  obtain ⟨hs, -, -, hU, -, -, -, β, hβs, hβk, hβe⟩ := h
  let e : (↥(FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).sec ⧸
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).ker.subgroupOf
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).sec) ≃*
        Multiplicative (Fin 3 → F) :=
    ((QuotientGroup.quotientMulEquivOfEq (show (FFModel.nat
        (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).ker.subgroupOf
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).sec = ⊥ from
          Subgroup.bot_subgroupOf _)).trans QuotientGroup.quotientBot).trans
      Subgroup.topEquiv
  refine ⟨hs, hU, e.toMonoidHom.comp β, e.surjective.comp hβs, fun u => ?_, fun γ u hu => ?_⟩
  · show e (β u) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact hβk u
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have h1 := hβe γ u m hu (Subgroup.mem_top _) hm.symm
    show e (β ⟨_, hu⟩) = Multiplicative.ofAdd (_ *ᵥ Multiplicative.toAdd (e (β u)))
    refine (congrArg e h1).trans ?_
    rw [← hm]
    rfl

theorem exists_hom_range {A B C : Type*} [Group A] [Group B] [Group C] (f : A →* B)
    (g : A →* C) (h : f.ker ≤ g.ker) : ∃ ψ : ↥f.range →* C, ∀ a, ψ ⟨f a, a, rfl⟩ = g a := by
  refine ⟨(QuotientGroup.lift f.ker g h).comp
    (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom, fun a => ?_⟩
  have e : (QuotientGroup.quotientKerEquivRange f).symm ⟨f a, a, rfl⟩ =
      (a : A ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e]
  rfl

theorem ker_eq_pCore_of_statedSL3 {X : Type*} [Group X] [Finite X] [Finite F] {n : ℕ}
    (hn : Even n) (hF : Nat.card F = 2 ^ n)
    (ψ : X →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (hψ : Function.Surjective ψ)
    (hk : IsPGroup 2 ψ.ker) : ψ.ker = CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (le_sSup ⟨MonoidHom.normal_ker ψ, hk⟩) ?_
  have hn1 := R3c2.one_le_of_natCard_eq_two_pow hF
  have h4 : 4 ≤ Nat.card F := by
    obtain ⟨m, hm⟩ := hn
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq := Vol2.Ch10.a319Facts_holds.sl3.1 F h4
  have : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hPn : ((CFSG.pCore 2 X).map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
  have hPp : IsPGroup 2 ((CFSG.pCore 2 X).map ψ) := CFSG.pCore_isPGroup.map ψ
  have hbot : (CFSG.pCore 2 X).map ψ = ⊥ := by
    obtain ⟨k, hk'⟩ := hPp.exists_card_eq
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
      ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩ ((CFSG.pCore 2 X).map ψ) with hc | ht
    · have hd : Nat.card ↥((CFSG.pCore 2 X).map ψ) ∣ 3 := by
        refine (Subgroup.card_dvd_of_le hc).trans ?_
        rw [← Subgroup.map_center_eq (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F),
          Subgroup.card_map_of_injective
            (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).injective]
        exact Vol2.Ch11.SecA.C10KH.card_center_sl3_dvd F
      rw [hk'] at hd
      have hk0 : k = 0 := by
        by_contra hk0
        have h2 : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans hd
        omega
      rw [hk0, pow_zero] at hk'
      exact Subgroup.eq_bot_of_card_eq _ hk'
    · exfalso
      obtain ⟨ω, hω3, hω1⟩ := R3c.exists_cube_root_of_card_two_pow hn hF
      have ho : orderOf (scal3 ω hω3) = 3 :=
        orderOf_eq_prime (scal3_pow_three ω hω3) (scal3_ne_one ω hω3 hω1)
      have h3 := orderOf_dvd_natCard (scal3 ω hω3)
      rw [ho] at h3
      rw [← Subgroup.card_top, ← ht, hk'] at h3
      have := Nat.prime_three.dvd_of_dvd_pow h3
      omega
  rw [Subgroup.map_eq_bot_iff] at hbot
  exact hbot

end A6L76Z

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem secAct_mem_commV {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hKH : K ≤ H) {h : ↥H}
    (hhK : ∀ k ∈ K, (h : G) * k * (h : G)⁻¹ ∈ K)
    {s : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))}
    (hs : s ∈ commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) :
    A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH) h s ∈
      commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  set φ := A6Mod.secAct hHU hHV h with hφ
  induction hs using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    obtain ⟨⟨k, hkH⟩, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hx
    have hk' : (h : G) * k * (h : G)⁻¹ ∈ K := hhK k hkK
    have hmem : A6Mod.secAct hHU hHV (h * ⟨k, hkH⟩ * h⁻¹) ∈
        autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :=
      (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, hk', rfl⟩
    have e : φ (A6Mod.secAct hHU hHV ⟨k, hkH⟩ v * v⁻¹) =
        A6Mod.secAct hHU hHV (h * ⟨k, hkH⟩ * h⁻¹) (φ v) * (φ v)⁻¹ := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply,
        MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rw [e]
    exact Subgroup.subset_closure ⟨_, hmem, φ v, rfl⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem normal_commV_map {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
    [((fsuV1 T V).subgroupOf H).Normal] {K : Subgroup G} (hKH : K ≤ H)
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) :
    ((commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))).map (secEmb hH)).Normal := ⟨fun v hv g => by
  obtain ⟨s, hs, rfl⟩ := hv
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective ((fsuV1 T V).subgroupOf H) g
  refine ⟨_, S.secAct_mem_commV hH hKH (fun k hk => hHK h h.2 k hk) hs, ?_⟩
  rw [secEmb_secAct]
  rfl⟩

theorem isElemAbelian_commV_map {H : Subgroup G} (hH : H ∈ S.Hz)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) [IsMulCommutative ↥(conjClosure S.V3 H)]
    [((fsuV1 T V).subgroupOf H).Normal] {K : Subgroup G} :
    IsElemAbelian 2 ((commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))).map (secEmb hH)) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨s, -, hs⟩ := a.2
    obtain ⟨t, -, ht⟩ := b.2
    show (a : ↥H ⧸ (fsuV1 T V).subgroupOf H) * b = b * a
    rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨s, -, rfl⟩ := hx
    rw [← map_pow, sq, sec_mul_self hab s, map_one]

theorem a319Hyp_of_even (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] [((fsuV1 T V).subgroupOf H).Normal]
    {K : Subgroup G} (hK : K ∈ cComp H) (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    {Kt : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))}
    (hKt : Kt = autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : Even n) (hF2 : Nat.card F = 2 ^ n)
    {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) →* ↥Kt}
    (hπi : Function.Injective π) (hπs : Function.Surjective π)
    {β : ↥(commV Kt) →* Multiplicative (Fin 3 → F)}
    (hβi : Function.Injective β) (hβs : Function.Surjective β)
    (hβe : ∀ (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (u : ↥(commV Kt))
      (hu : ((π γ : ↥Kt) : MulAut _) (u : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ∈ commV Kt),
      β ⟨_, hu⟩ = Multiplicative.ofAdd ((((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ
        Multiplicative.toAdd (β u))) :
    A319Hyp ((K.subgroupOf H).map (QuotientGroup.mk' ((fsuV1 T V).subgroupOf H)))
      ((commV Kt).map (secEmb hH)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  set N := (fsuV1 T V).subgroupOf H with hN
  set q := QuotientGroup.mk' N with hq
  set Kh := (K.subgroupOf H).map q with hKh
  set Vh := (commV Kt).map (secEmb hH) with hVh
  have hVhn : Vh.Normal := by
    rw [hVh, hKt]
    exact normal_commV_map hH hKH hHK
  obtain ⟨ψ₀, hψ₀π, hψ₀s⟩ : ∃ ψ₀ : ↥(K.subgroupOf H) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F),
      (∀ x, ((π (ψ₀ x) : ↥Kt) : MulAut _) = A6Mod.secAct hHU hHV (x : ↥H)) ∧
        Function.Surjective ψ₀ := by
    let κ₀ : ↥(K.subgroupOf H) →* ↥Kt :=
      ((A6Mod.secAct hHU hHV).comp (K.subgroupOf H).subtype).codRestrict Kt
        (fun x => hKt ▸ (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, x.2, rfl⟩)
    let πe := MulEquiv.ofBijective π ⟨hπi, hπs⟩
    refine ⟨πe.symm.toMonoidHom.comp κ₀, fun x => ?_, fun γ => ?_⟩
    · have : π (πe.symm (κ₀ x)) = κ₀ x := πe.apply_symm_apply _
      exact congrArg Subtype.val this
    · have hγ : ((π γ : ↥Kt) : MulAut _) ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := hKt ▸ (π γ).2
      obtain ⟨f, hfK, hf⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hγ
      refine ⟨⟨f, hfK⟩, ?_⟩
      have : κ₀ ⟨f, hfK⟩ = π γ := Subtype.ext hf
      show πe.symm (κ₀ ⟨f, hfK⟩) = γ
      rw [this]
      exact πe.symm_apply_apply γ
  have hle : (q.comp (K.subgroupOf H).subtype).ker ≤ ψ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxV : ((x : ↥H) : G) ∈ fsuV1 T V := by
      rw [MonoidHom.comp_apply, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      exact hx
    have hκ : A6Mod.secAct hHU hHV (x : ↥H) = 1 := by
      rw [A6Mod.secAct_eq_one_iff]
      intro u hu
      have huz : S.z * u = u * S.z := (Subgroup.mem_centralizer_singleton_iff.1
        (show u ∈ Subgroup.centralizer ({S.z} : Set G) from hH.2.1 (UH_le_H hH hu))).symm
      rcases S.mem_V1_iff.1 hxV with h | h
      · rw [h]
        simp only [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [h, huz, mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
    rw [← hψ₀π] at hκ
    apply hπi
    rw [map_one]
    exact Subtype.ext hκ
  have hrange : (q.comp (K.subgroupOf H).subtype).range = Kh := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨ψ₁, hψ₁⟩ := A6L76Z.exists_hom_range _ ψ₀ hle
  set ψ : ↥Kh →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
    ψ₁.comp (MulEquiv.subgroupCongr hrange).symm.toMonoidHom with hψ
  have hψmk : ∀ (x : ↥(K.subgroupOf H)) (hx : q x ∈ Kh), ψ ⟨q x, hx⟩ = ψ₀ x := fun x hx =>
    hψ₁ x
  have hmemKh : ∀ x : ↥(K.subgroupOf H), q x ∈ Kh := fun x => by
    rw [hKh]
    exact ⟨(x : ↥H), x.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    intro γ
    obtain ⟨x, hx⟩ := hψ₀s γ
    exact ⟨⟨q x, hmemKh x⟩, by rw [hψmk, hx]⟩
  have hKhmem : ∀ l : ↥Kh, ∃ x : ↥(K.subgroupOf H), (l : ↥H ⧸ N) = q x := by
    rintro ⟨l, hl⟩
    rw [hKh] at hl
    obtain ⟨x, hx, rfl⟩ := hl
    exact ⟨⟨x, hx⟩, rfl⟩
  have hk2 : IsPGroup 2 ψ.ker := by
    rintro ⟨l, hl⟩
    obtain ⟨x, hlx⟩ := hKhmem l
    have hl1 : ψ l = 1 := hl
    have e1 : l = ⟨q x, hmemKh x⟩ := Subtype.ext hlx
    rw [e1, hψmk] at hl1
    have h1 : A6Mod.secAct hHU hHV (x : ↥H) = 1 := by
      rw [← hψ₀π, hl1, map_one]
      rfl
    have hxQ : ((x : ↥H) : G) ∈ pCoreOf 2 H :=
      (S.mem_QH_iff_tilde hNS h13315 h1356two hH (x : ↥H).2).2
        ((A6Mod.secAct_eq_one_iff hHU hHV _).1 h1)
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hxQ⟩
    refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
    have hj' : (x : ↥H) ^ 2 ^ j = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
    show (l : ↥H ⧸ N) ^ 2 ^ j = 1
    rw [hlx, ← map_pow, hj', map_one]
  have hker : ψ.ker = CFSG.pCore 2 ↥Kh := A6L76Z.ker_eq_pCore_of_statedSL3 hn hF2 ψ hψs hk2
  set φ : ↥Kh ⧸ CFSG.pCore 2 ↥Kh ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs) with hφ
  have hφmk : ∀ l : ↥Kh, φ (QuotientGroup.mk l) = ψ l := fun l => rfl
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥Vh ≃* Multiplicative (Fin 3 → F), ∀ (s) (hs : s ∈ commV Kt)
      (hv : secEmb hH s ∈ Vh), θ ⟨secEmb hH s, hv⟩ = β ⟨s, hs⟩ := by
    refine ⟨((commV Kt).equivMapOfInjective (secEmb hH) (secEmb_injective hH)).symm.trans
      (MulEquiv.ofBijective β ⟨hβi, hβs⟩), fun s hs hv => ?_⟩
    have e : ((commV Kt).equivMapOfInjective (secEmb hH) (secEmb_injective hH)).symm
        ⟨secEmb hH s, hv⟩ = ⟨s, hs⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [MulEquiv.trans_apply, e]
    rfl
  have hVhmem : ∀ v : ↥Vh, ∃ s, ∃ hs : s ∈ commV Kt, (v : ↥H ⧸ N) = secEmb hH s := by
    rintro ⟨v, hv⟩
    rw [hVh] at hv
    obtain ⟨s, hs, rfl⟩ := hv
    exact ⟨s, hs, rfl⟩
  have hHyp : A319Hyp Kh Vh := by
    refine ⟨n, 1, F, inferInstance, inferInstance, φ, hn, hF2, le_rfl, by norm_num,
      fun _ => Vh, fun _ => le_rfl, iSup_const.symm, iSupIndep_subsingleton _,
      fun _ => ⟨θ, fun l v => ?_⟩⟩
    obtain ⟨x, hlx⟩ := hKhmem l
    obtain ⟨s, hs, hvs⟩ := hVhmem v
    have hmem : (l : ↥H ⧸ N) * (v : ↥H ⧸ N) * (l : ↥H ⧸ N)⁻¹ ∈ Vh :=
      hVhn.conj_mem _ v.2 _
    refine ⟨⟨_, hmem⟩, rfl, ?_⟩
    have hs' : A6Mod.secAct hHU hHV (x : ↥H) s ∈ commV Kt := by
      rw [hKt] at hs ⊢
      exact S.secAct_mem_commV hH hKH (fun k hk => hHK _ (x : ↥H).2 k hk) hs
    have hconj : (l : ↥H ⧸ N) * (v : ↥H ⧸ N) * (l : ↥H ⧸ N)⁻¹ =
        secEmb hH (A6Mod.secAct hHU hHV (x : ↥H) s) := by
      rw [secEmb_secAct, hlx, hvs]
      rfl
    have hv1 : v = ⟨secEmb hH s, hvs ▸ v.2⟩ := Subtype.ext hvs
    have hv2 : (⟨_, hmem⟩ : ↥Vh) = ⟨secEmb hH (A6Mod.secAct hHU hHV (x : ↥H) s),
        hconj ▸ hmem⟩ := Subtype.ext hconj
    have hs'' : ((π (ψ₀ x) : ↥Kt) : MulAut _) s ∈ commV Kt := by rw [hψ₀π]; exact hs'
    have e2 : (⟨_, hs'⟩ : ↥(commV Kt)) = ⟨_, hs''⟩ := Subtype.ext (by
      show (A6Mod.secAct hHU hHV (x : ↥H)) s = ((π (ψ₀ x) : ↥Kt) : MulAut _) s
      rw [hψ₀π])
    have e3 : (l : ↥Kh) = ⟨q x, hmemKh x⟩ := Subtype.ext hlx
    have st1 : θ ⟨_, hmem⟩ = β ⟨_, hs'⟩ := by
      rw [hv2]
      exact hθ _ hs' _
    have st4 : θ v = β ⟨s, hs⟩ := by
      rw [hv1]
      exact hθ _ hs _
    have st5 : φ (QuotientGroup.mk l) = ψ₀ x := by rw [hφmk, e3, hψmk]
    have st3 := hβe (ψ₀ x) ⟨s, hs⟩ hs''
    exact st1.trans ((congrArg β e2).trans (st3.trans (by rw [← st4, ← st5])))
  exact hHyp

end Setting4

open Setting4 in
theorem lem1376L1KSmallEven_of (hF : A318Facts)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two) :
    Lem1376L1KSmallEven := by
  intro G _ _ T L V S hNS hNU H hH hab _ K hK n hn hSL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  set Kt := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) with hKt
  obtain ⟨F, _, _, hF2, π₀, hR⟩ := id hSL
  set π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) →* ↥Kt := π₀ with hπ
  have hπi : Function.Injective π := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hR
  obtain ⟨hπs, hKU, β, hβs, hβk, hβe⟩ := A6L76Z.natRealizes_clean (π := π) hR
  obtain ⟨ω, hω3, hω1⟩ := R3c.exists_cube_root_of_card_two_pow hn hF2
  have hω1' : (ω : F) ≠ 1 := fun h => hω1 (Units.ext h)
  set z₀ := A6L76Z.scal3 ω hω3 with hz₀
  have hz₀3 : z₀ ^ 3 = 1 := by
    refine A6L76M.ext_val fun v => ?_
    funext i
    rw [pow_three, A6L76M.val_mul, A6L76M.val_mul, hz₀, A6L76Z.scal3_val,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec_diagonal, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]
    rw [← mul_assoc, ← mul_assoc, ← pow_two, ← pow_succ, ← Units.val_pow_eq_pow_val, hω3,
      Units.val_one, one_mul]
  have hZ : fixV Kt ⊓ commV Kt = ⊥ := by
    refine fixV_inf_commV_eq_bot (sec_mul_self hab) (S.isPerfect_tilde hH hK) (π z₀).2
      (fun y hy => ?_) ?_ (fun u hu hζu => ?_)
    · obtain ⟨γ, hγ⟩ := hπs ⟨y, hy⟩
      have h1 : π z₀ * π γ = π γ * π z₀ := by
        rw [← map_mul, ← map_mul, A6L76Z.scal3_comm]
      have h2 := congrArg Subtype.val h1
      rw [hγ] at h2
      exact h2
    · have h1 : (π z₀) ^ 3 = 1 := by rw [← map_pow, hz₀3, map_one]
      exact congrArg Subtype.val h1
    · have hu' : ((π z₀ : ↥Kt) : MulAut _) u ∈ commV Kt := hKU (π z₀) u hu
      have h1 := hβe z₀ ⟨u, hu⟩ hu'
      have e1 : (⟨((π z₀ : ↥Kt) : MulAut _) u, hu'⟩ : ↥(commV Kt)) = ⟨u, hu⟩ :=
        Subtype.ext hζu
      rw [e1] at h1
      have h5 : β ⟨u, hu⟩ = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        have h6 := congrFun (congrArg Multiplicative.toAdd h1) i
        simp only [toAdd_ofAdd, hz₀, A6L76Z.scal3_val, Matrix.mulVec_diagonal] at h6
        have h7 : ((ω : F) - 1) * Multiplicative.toAdd (β ⟨u, hu⟩) i = 0 := by
          rw [sub_mul, one_mul, ← h6, sub_self]
        rcases mul_eq_zero.1 h7 with h8 | h8
        · exact absurd (sub_eq_zero.1 h8) hω1'
        · rw [h8]
          rfl
      exact ((hβk ⟨u, hu⟩).1 h5).1
  obtain ⟨eK⟩ := S.exists_quotEquiv_of_realizes hNS h13315 h1356two hH hK
    (FFModel.nat_faithful _) ⟨π₀, hR⟩
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  have hK₀ : K.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp hK
  have hrank : 1 < CFSG.Open.pRank 3 (K.subgroupOf H) := by
    rw [Vol2.Ch11.SecA.pRank_subgroupOf_eq hKH Nat.prime_three (by norm_num)]
    have : Finite (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).Gam :=
      Finite.of_equiv _ eK.toEquiv
    have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eK
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) = 2 :=
      R3c.pRank_three_statedSL_three_even hn hF2
    have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) = 2 := h1.trans h2
    omega
  have hKn : (K.subgroupOf H).Normal := A318.normal_of_pRank_gt_one hSQ
    (h38 _ (SQTKHyp.of_sqtkGroup ↥H hSQ)) hK₀ Nat.prime_three (by norm_num) hrank
  have hHK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := fun h hh k hk => by
    have := Subgroup.mem_subgroupOf.1 (hKn.conj_mem ⟨k, hKH hk⟩ hk ⟨h, hh⟩)
    simpa using this
  have := normal_V1_subgroupOf hH
  set N := (fsuV1 T V).subgroupOf H with hN
  set q := QuotientGroup.mk' N with hq
  have hV1p : IsPGroup 2 ↥(fsuV1 T V) := IsPGroup.of_card (n := 1) (by rw [S.card_V1]; norm_num)
  have hN2 : IsPGroup 2 ↥N := hV1p.comap_of_injective H.subtype H.subtype_injective
  have hSQh : SQTKGroup (↥H ⧸ N) := sqtkGroup_quotient_of_isPGroup_two hSQ N hN2
  set Kh := (K.subgroupOf H).map q with hKh
  have hKhc : Kh ∈ cComp (⊤ : Subgroup (↥H ⧸ N)) := by
    refine map_mem_cComp_top_of_ne_bot q (QuotientGroup.mk'_surjective N) hK₀ ?_
    intro hbot
    apply not_isSolvable_of_mem_cComp hK
    have hle : K ≤ fsuV1 T V := by
      intro k hk
      have h1 : q ⟨k, hKH hk⟩ ∈ (K.subgroupOf H).map q := ⟨⟨k, hKH hk⟩, hk, rfl⟩
      rw [hbot, Subgroup.mem_bot, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have : Group.IsNilpotent ↥K := (hV1p.to_le hle).isNilpotent
    infer_instance
  set Vh := (commV Kt).map (secEmb hH) with hVh
  have hVhn : Vh.Normal := normal_commV_map hH hKH hHK
  have hVhab : IsElemAbelian 2 Vh := isElemAbelian_commV_map hH hab
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (hβk u).1 hu
    rw [hZ, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hHyp : A319Hyp Kh Vh :=
    a319Hyp_of_even hNS h13315 h1356two hH hK hHK hKt hn hF2 hπi hπs hβi hβs hβe
  have hQh := SQTKHyp.of_sqtkGroup (↥H ⧸ N) hSQh
  have h319 := a319 hF Vol2.Ch10.a319Facts_holds hSQh (h36 _ hQh) (h38 _ hQh) hKhc hVhn hVhab
    hHyp
  refine (S.L1_le_oPrimeResidualOf hH).trans ((Subgroup.closure_le _).2 ?_)
  rintro x ⟨hxH, j, hj⟩
  have hqx : q ⟨x, hxH⟩ ∈ oPrimeResidualOf 3 (⊤ : Subgroup (↥H ⧸ N)) := by
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, ?_⟩
    have hd : orderOf (q ⟨x, hxH⟩) ∣ 3 ^ j := by
      rw [← hj]
      refine (orderOf_map_dvd q _).trans ?_
      rw [Subgroup.orderOf_mk]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    exact ⟨i, hi⟩
  rw [← h319, hKh] at hqx
  obtain ⟨y, hyK, hy⟩ := hqx
  have hv : (y : G)⁻¹ * x ∈ fsuV1 T V := by
    have h1 := QuotientGroup.eq.1 hy
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hyK' : (y : G) ∈ K := hyK
  have hxv : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rcases S.mem_V1_iff.1 hv with h1 | h1
  · rw [hxv, h1, mul_one]
    exact hyK'
  · have hyz : (y : G) * S.z = S.z * y := Subgroup.mem_centralizer_singleton_iff.1
      (show (y : G) ∈ Subgroup.centralizer ({S.z} : Set G) from hH.2.1 y.2)
    have hz2 : S.z ^ 2 = 1 := by rw [← S.orderOf_z]; exact pow_orderOf_eq_one _
    have hx3 : x ^ 3 ^ j = 1 := by rw [← hj]; exact pow_orderOf_eq_one x
    obtain ⟨m, hm⟩ : Odd (3 ^ j) := Odd.pow (by decide)
    have hzm : S.z ^ (3 ^ j) = S.z := by
      rw [hm, pow_succ, pow_mul, hz2, one_pow, one_mul]
    have hyj : (y : G) ^ (3 ^ j) * S.z = 1 := by
      have h2 : ((y : G) * S.z) ^ (3 ^ j) = (y : G) ^ (3 ^ j) * S.z ^ (3 ^ j) :=
        (Commute.mul_pow hyz _)
      rw [hzm] at h2
      rw [← h2, ← h1, ← hxv, hx3]
    have hzK : S.z ∈ K := by
      have h3 : S.z = ((y : G) ^ (3 ^ j))⁻¹ := (eq_inv_of_mul_eq_one_right hyj)
      rw [h3]
      exact K.inv_mem (K.pow_mem hyK' _)
    rw [hxv, h1]
    exact K.mul_mem hyK' hzK


end CFSG.Quasithin.H13.A6
