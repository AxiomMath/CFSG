module

public import CFSG.RankThree.S4Free.Stellmacher34Cent
public import CFSG.RankThree.S4Free.Stellmacher34Defs
public import CFSG.RankThree.S4Free.Stellmacher28
import CFSG.RankThree.S4Free.Stellmacher33
import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.RankThree.S4Free.Stell34

open Subgroup CFSG.Blueprint CFSG.Quasithin
open CFSG.RankThree.S4Free.Stell33 (LCfgCore)
open scoped commutatorElement Pointwise

section Module

variable {Λ : Type*} [Group Λ]

abbrev ModPD (P D : Subgroup Λ) : Type _ := ↥P ⧸ D.subgroupOf P

variable {P D : Subgroup Λ}

abbrev modCommGroup [(D.subgroupOf P).Normal]
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ D) : CommGroup (ModPD P D) :=
  { (inferInstance : Group (ModPD P D)) with
    mul_comm := by
      intro a b
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      have e : (((x * y)⁻¹ * (y * x) : ↥P) : Λ) =
          (y : Λ)⁻¹ * (x : Λ)⁻¹ * ((y : Λ)⁻¹)⁻¹ * ((x : Λ)⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      rw [e]
      exact hPc _ (inv_mem y.2) _ (inv_mem x.2) }

theorem map_conjNormal_subgroupOf [P.Normal] [D.Normal] (g : Λ) :
    (D.subgroupOf P).map ((MulAut.conjNormal (H := P) g : MulAut P) : ↥P →* ↥P) =
      D.subgroupOf P := by
  ext y
  simp only [mem_map, mem_subgroupOf, MonoidHom.coe_coe]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [MulAut.conjNormal_apply]
    exact (inferInstance : D.Normal).conj_mem _ hz g
  · intro hy
    refine ⟨(MulAut.conjNormal g⁻¹ : MulAut P) y, ?_, ?_⟩
    · rw [MulAut.conjNormal_apply]
      exact (inferInstance : D.Normal).conj_mem _ hy g⁻¹
    · rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

@[expose] noncomputable def modAct [P.Normal] [D.Normal] : Λ →* MulAut (ModPD P D) where
  toFun g := QuotientGroup.congr (D.subgroupOf P) (D.subgroupOf P) (MulAut.conjNormal g)
    (map_conjNormal_subgroupOf g)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with | H x => ?_
    rw [QuotientGroup.congr_mk, map_one, MulAut.one_apply, MulAut.one_apply]
  map_mul' g h := by
    ext q
    induction q using QuotientGroup.induction_on with | H x => ?_
    rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
      map_mul, MulAut.mul_apply]

theorem modAct_mk [P.Normal] [D.Normal] (g : Λ) (x : P) :
    modAct (P := P) (D := D) g (x : ModPD P D) =
      ((MulAut.conjNormal g x : P) : ModPD P D) :=
  rfl

theorem mk_eq_mk_iff {x y : P} : (x : ModPD P D) = (y : ModPD P D) ↔ (x : Λ)⁻¹ * y ∈ D := by
  rw [QuotientGroup.eq, mem_subgroupOf]
  rfl

end Module

namespace SzCfg

open CFSG.RankThree.S4Free.Stell33.LCfg (Wu A B D X)

universe u

variable {Λ : Type u} [Group Λ] [Finite Λ] {T W R : Subgroup Λ} {a : ℕ} {K : Type} [Field K]
  [Finite K] {φ : Λ →* suzukiGroup a K} {u : Λ}

theorem normal_D (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u) :
    (D W (oTwo Λ) u).Normal := by
  refine ⟨fun d hd g => ?_⟩
  have hgd := mem_centralizer_iff.mp (hc.L_le_centralizer_D (mem_top g)) d hd
  rw [← hgd, mul_inv_cancel_right]
  exact hd

theorem comm_oTwo_mem_D (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u)
    (hX : oTwo Λ = X W (oTwo Λ) u) :
    ∀ x ∈ oTwo Λ, ∀ y ∈ oTwo Λ, x * y * x⁻¹ * y⁻¹ ∈ D W (oTwo Λ) u := by
  intro x hx y hy
  rw [hX] at hx hy
  exact hc.comm_X_mem_D hx hy

theorem sq_oTwo_mem_D (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u)
    (hX : oTwo Λ = X W (oTwo Λ) u) {x : Λ} (hx : x ∈ oTwo Λ) : x * x ∈ D W (oTwo Λ) u := by
  rw [hX] at hx
  exact hc.sq_X_mem_D hx

theorem normalizer_A_le (h : SzCfg T W R φ) (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u)
    (hX : oTwo Λ = X W (oTwo Λ) u) (hC : centralizer (oTwo Λ : Set Λ) ≤ oTwo Λ) :
    normalizer (A W (oTwo Λ) : Set Λ) ≤ normalizer (W : Set Λ) := by
  intro g hg
  by_contra hgW
  have hsup := h.sup_conj g hgW
  have hWA : W ≤ normalizer (A W (oTwo Λ) : Set Λ) :=
    Stell33.le_normalizer_of_forall_conj_mem fun w hw y hy => by
      rw [h.comm_W hw hy.1, mul_inv_cancel_right]
      exact hy
  have hWgA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (A W (oTwo Λ) : Set Λ) := by
    rintro _ ⟨w, hw, rfl⟩
    exact mul_mem (mul_mem hg (hWA hw)) (inv_mem hg)
  have hAn : (A W (oTwo Λ)).Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le hWA hWgA
  have hB : B W (oTwo Λ) u = A W (oTwo Λ) := by
    rw [← hc.map_conj_A]
    exact Stell33.map_conj_eq_of_mem_normalizer
      (by rw [normalizer_eq_top_iff.mpr hAn]; exact mem_top u)
  have hXA : oTwo Λ ≤ W := by
    rw [hX, X, hB, sup_idem]
    exact inf_le_left
  apply h.not_le_oTwo
  intro w hw
  refine hC (mem_centralizer_iff.mpr fun x hx => ?_)
  exact h.comm_W (hXA hx) hw

theorem ker_modAct (h : SzCfg T W R φ) (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u)
    (hR : R = oTwo Λ) (hX : oTwo Λ = X W (oTwo Λ) u)
    (hC : centralizer (oTwo Λ : Set Λ) ≤ oTwo Λ) :
    haveI := normal_D hc
    (modAct (P := oTwo Λ) (D := D W (oTwo Λ) u)).ker = oTwo Λ := by
  haveI hDn := normal_D hc
  set Dd := D W (oTwo Λ) u with hDd
  apply le_antisymm
  · set K₁ := (modAct (P := oTwo Λ) (D := Dd)).ker with hK₁
    have hcomm : ∀ y ∈ oTwo Λ, ∀ k ∈ K₁, ⁅y, k⁆ ∈ Dd := by
      intro y hy k hk
      have h1 : modAct (P := oTwo Λ) (D := Dd) k ((⟨y, hy⟩ : oTwo Λ) : ModPD (oTwo Λ) Dd) =
          ((⟨y, hy⟩ : oTwo Λ) : ModPD (oTwo Λ) Dd) := by
        rw [MonoidHom.mem_ker.mp hk, MulAut.one_apply]
      rw [modAct_mk, mk_eq_mk_iff, MulAut.conjNormal_apply] at h1
      have h2 := hDn.conj_mem _ h1 y
      rw [commutatorElement_def]
      convert h2 using 1
      group
    have h2 : ⁅oTwo Λ, K₁⁆ ≤ Dd := commutator_le.mpr hcomm
    have h3 : ⁅⁅oTwo Λ, K₁⁆, K₁⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine (commutator_mono h2 le_rfl).trans ?_
      rw [le_bot_iff, commutator_eq_bot_iff_le_centralizer]
      intro d hd
      rw [mem_centralizer_iff]
      intro k _
      exact (mem_centralizer_iff.mp (hc.L_le_centralizer_D (mem_top k)) d hd).symm
    have h4 : ⁅⁅K₁, oTwo Λ⁆, K₁⁆ = ⊥ := by rw [commutator_comm K₁]; exact h3
    have h5 : ⁅⁅K₁, K₁⁆, oTwo Λ⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h4 h3
    rw [commutator_eq_bot_iff_le_centralizer] at h5
    exact h.le_oTwo_of_commutator_le hR (h5.trans hC)
  · intro x hx
    rw [MonoidHom.mem_ker]
    ext q
    induction q using QuotientGroup.induction_on with | H y => ?_
    rw [modAct_mk, MulAut.one_apply, mk_eq_mk_iff, MulAut.conjNormal_apply]
    have := comm_oTwo_mem_D hc hX x hx _ (inv_mem y.2)
    convert this using 1
    simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem nonempty_range_mulEquiv (h : SzCfg T W R φ)
    (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u) (hR : R = oTwo Λ)
    (hX : oTwo Λ = X W (oTwo Λ) u) (hC : centralizer (oTwo Λ : Set Λ) ≤ oTwo Λ) :
    haveI := normal_D hc
    Nonempty (↥(modAct (P := oTwo Λ) (D := D W (oTwo Λ) u)).range ≃* suzukiGroup a K) := by
  haveI := normal_D hc
  have hk : (modAct (P := oTwo Λ) (D := D W (oTwo Λ) u)).ker = φ.ker := by
    rw [ker_modAct h hc hR hX hC, h.ker_eq, hR]
  exact ⟨(QuotientGroup.quotientKerEquivRange _).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ h.surjective))⟩

theorem oTwo_range_eq_bot (h : SzCfg T W R φ)
    (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u) (hR : R = oTwo Λ)
    (hX : oTwo Λ = X W (oTwo Λ) u) (hC : centralizer (oTwo Λ : Set Λ) ≤ oTwo Λ) :
    haveI := normal_D hc
    oTwo ↥(modAct (P := oTwo Λ) (D := D W (oTwo Λ) u)).range = ⊥ := by
  haveI := normal_D hc
  obtain ⟨e⟩ := nonempty_range_mulEquiv h hc hR hX hC
  obtain ⟨-, -, hs⟩ := CFSG.LieType.Ree.suzuki_simple h.one_le h.card_K
  haveI := hs
  haveI : IsSimpleGroup ↥(modAct (P := oTwo Λ) (D := D W (oTwo Λ) u)).range := e.isSimpleGroup
  rcases (inferInstance : (oTwo ↥(modAct (P := oTwo Λ) (D := D W (oTwo Λ) u)).range).Normal
    ).eq_bot_or_eq_top with h1 | h1
  · exact h1
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 := Stell.oTwo_isPGroup ↥(modAct (P := oTwo Λ) (D := D W (oTwo Λ) u)).range
    rw [h1] at h2
    exact not_isPGroup_suzuki h.one_le h.card_K
      ((h2.of_equiv Subgroup.topEquiv).of_equiv e)

theorem isL24Sz_image (h : SzCfg T W R φ) (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u)
    (hR : R = oTwo Λ) (hX : oTwo Λ = X W (oTwo Λ) u)
    (hC : centralizer (oTwo Λ : Set Λ) ≤ oTwo Λ) :
    haveI := normal_D hc
    Stell.IsL24Sz (T.map (modAct (P := oTwo Λ) (D := D W (oTwo Λ) u)))
      ((normalizer (W : Set Λ)).map (modAct (P := oTwo Λ) (D := D W (oTwo Λ) u)))
      (W.map (modAct (P := oTwo Λ) (D := D W (oTwo Λ) u)))
      (modAct (P := oTwo Λ) (D := D W (oTwo Λ) u)).range := by
  haveI := normal_D hc
  set ρ := modAct (P := oTwo Λ) (D := D W (oTwo Λ) u) with hρ
  have hker := ker_modAct h hc hR hX hC
  have hkT : ρ.ker ≤ T := by rw [hker]; exact h.oTwo_le_T
  have hkN : ρ.ker ≤ normalizer (W : Set Λ) := hkT.trans h.T_le_normalizer
  obtain ⟨e⟩ := nonempty_range_mulEquiv h hc hR hX hC
  refine ⟨⟨map_le_range ρ W, ?_, ?_, ?_⟩, ?_⟩
  · intro hle
    apply h.normalizer_ne_top
    rw [eq_top_iff]
    intro g _
    obtain ⟨n, hn, hng⟩ := hle (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    have h1 : n⁻¹ * g ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hng, inv_mul_cancel]
    have := mul_mem hn (hkN h1)
    rwa [mul_inv_cancel_left] at this
  · rw [MonoidHom.range_eq_map, relIndex_map_map, sup_eq_left.mpr hkT, top_sup_eq,
      relIndex_top_right]
    exact h.not_dvd_index
  · rintro _ ⟨g, rfl⟩ hg
    have hgN : g ∉ normalizer (W : Set Λ) := fun hgN => hg (mem_map_of_mem ρ hgN)
    have h1 := congrArg (Subgroup.map ρ) (h.sup_conj g hgN)
    rw [Subgroup.map_sup, Subgroup.map_map, ← MonoidHom.range_eq_map] at h1
    rw [← h1, Subgroup.map_map, show (MulAut.conj (ρ g)).toMonoidHom.comp ρ =
      ρ.comp (MulAut.conj g).toMonoidHom from MonoidHom.ext fun w => by simp [MulAut.conj_apply]]
  · refine ⟨⊥, inferInstance, ?_, ?_, a, h.one_le, K, inferInstance, inferInstance, h.card_K,
      ⟨QuotientGroup.quotientBot.trans e⟩⟩
    · rw [oTwo_range_eq_bot h hc hR hX hC]
    · rw [oTwo_range_eq_bot h hc hR hX hC, relIndex_self]
      norm_num

theorem nontrivial_sz (n : ℕ) : Nontrivial (CFSG.Open.Sz n) := by
  refine ⟨⟨SzNatural.rootElt n 1 0, 1, fun he => ?_⟩⟩
  rw [← SzNatural.rootElt_zero_zero, SzNatural.rootElt_inj] at he
  exact one_ne_zero he.1

theorem isNatSzExt (h : SzCfg T W R φ) (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u)
    (hR : R = oTwo Λ) (hX : oTwo Λ = X W (oTwo Λ) u)
    (hC : centralizer (oTwo Λ : Set Λ) ≤ oTwo Λ) (h25 : Hyp25dSz.{u}) :
    ∃ n, 1 ≤ n ∧ Stell.IsNatSzExt Λ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hDn := normal_D hc
  set Dd := D W (oTwo Λ) u with hDd
  letI : CommGroup (ModPD (oTwo Λ) Dd) := modCommGroup (comm_oTwo_mem_D hc hX)
  set ρ := modAct (P := oTwo Λ) (D := Dd) with hρ
  have hker : ρ.ker = oTwo Λ := ker_modAct h hc hR hX hC
  have hDA : Dd ≤ A W (oTwo Λ) := hc.D_le_A
  have hAP : A W (oTwo Λ) ≤ oTwo Λ := hc.A_le_P
  set Z₀ : Subgroup (ModPD (oTwo Λ) Dd) :=
    ((A W (oTwo Λ)).subgroupOf (oTwo Λ)).map (QuotientGroup.mk' (Dd.subgroupOf (oTwo Λ)))
    with hZ₀
  have hV2 : ∀ v : ModPD (oTwo Λ) Dd, v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, pow_two,
      Subgroup.coe_mul]
    exact sq_oTwo_mem_D hc hX x.2
  have hZA : Z₀ ≤ CFSG.Quasithin.fixV (W.map ρ) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨w, hw, rfl⟩
    have hxW : (x : Λ) ∈ W := (mem_subgroupOf.mp hx).1
    change ρ w ((x : ModPD (oTwo Λ) Dd)) = (x : ModPD (oTwo Λ) Dd)
    rw [hρ, modAct_mk]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, h.comm_W hw hxW, mul_inv_cancel_right]
  have hquad : CFSG.Quasithin.IsQuadratic (W.map ρ) := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨_, ⟨w, hw, rfl⟩, v, rfl⟩
    induction v using QuotientGroup.induction_on with | H y => ?_
    refine hZA ⟨MulAut.conjNormal w y * y⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
        MulAut.conjNormal_apply]
      exact hc.comm_P_W_mem_A y.2 hw
    · change _ = ρ w (y : ModPD (oTwo Λ) Dd) * (y : ModPD (oTwo Λ) Dd)⁻¹
      rw [hρ, modAct_mk, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hstab : ρ.range ⊓ CFSG.Quasithin.stabSub Z₀ ≤ (normalizer (W : Set Λ)).map ρ := by
    rintro _ ⟨⟨g, rfl⟩, hgs⟩
    refine mem_map_of_mem ρ (normalizer_A_le h hc hX hC ?_)
    have key : ∀ g' : Λ, ρ g' ∈ CFSG.Quasithin.stabSub Z₀ →
        ∀ x ∈ A W (oTwo Λ), g' * x * g'⁻¹ ∈ A W (oTwo Λ) := by
      intro g' hg' x hx
      have hxZ : ((⟨x, hAP hx⟩ : oTwo Λ) : ModPD (oTwo Λ) Dd) ∈ Z₀ :=
        ⟨⟨x, hAP hx⟩, mem_subgroupOf.mpr hx, rfl⟩
      have h1 := (hg' _).mpr hxZ
      rw [hρ, modAct_mk] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      rw [QuotientGroup.mk'_apply, mk_eq_mk_iff, MulAut.conjNormal_apply] at hyx
      have := mul_mem (mem_subgroupOf.mp hy) (hDA hyx)
      rwa [mul_inv_cancel_left] at this
    have hinv : ρ g⁻¹ ∈ CFSG.Quasithin.stabSub Z₀ := by
      rw [map_inv]
      exact inv_mem hgs
    refine Stell33.mem_normalizer_of_conj (key g hgs) fun x hx => ?_
    have := key g⁻¹ hinv x hx
    rwa [inv_inv] at this
  have hgen : ∀ U : Subgroup (ModPD (oTwo Λ) Dd), (∀ l ∈ ρ.range, Z₀.map l.toMonoidHom ≤ U) →
      U = ⊤ := by
    intro U hU
    have h1 : Z₀ ≤ U := by
      intro z hz
      have := hU 1 (one_mem _) ⟨z, hz, rfl⟩
      simpa using this
    have h2 := hU (ρ u) (MonoidHom.mem_range.mpr ⟨u, rfl⟩)
    rw [eq_top_iff]
    intro v _
    induction v using QuotientGroup.induction_on with | H x => ?_
    have hxX : (x : Λ) ∈ X W (oTwo Λ) u := hX ▸ x.2
    obtain ⟨a', ha', b', hb', hab⟩ := hc.mem_X_iff.mp hxX
    have hx : x = ⟨a', hAP ha'⟩ * ⟨b', hc.B_le_P hb'⟩ := Subtype.ext hab
    rw [hx, QuotientGroup.mk_mul]
    have hA1 : ((⟨a', hAP ha'⟩ : oTwo Λ) : ModPD (oTwo Λ) Dd) ∈ Z₀ :=
      ⟨⟨a', hAP ha'⟩, mem_subgroupOf.mpr ha', rfl⟩
    refine mul_mem (h1 hA1) (h2 ?_)
    have hb'' := hb'
    rw [← hc.map_conj_A] at hb''
    obtain ⟨a'', ha'', hab''⟩ := hb''
    have hA2 : ((⟨a'', hAP ha''⟩ : oTwo Λ) : ModPD (oTwo Λ) Dd) ∈ Z₀ :=
      ⟨⟨a'', hAP ha''⟩, mem_subgroupOf.mpr ha'', rfl⟩
    refine ⟨_, hA2, ?_⟩
    change ρ u _ = _
    rw [hρ, modAct_mk]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact hab''
  have hfix : CFSG.Quasithin.fixV ρ.range = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    induction v using QuotientGroup.induction_on with | H x => ?_
    rw [mem_bot, QuotientGroup.eq_one_iff, mem_subgroupOf]
    have hxX : (x : Λ) ∈ X W (oTwo Λ) u := hX ▸ x.2
    refine hc.mem_D_of_comm_mem_D hxX fun g _ => ?_
    have h1 := hv (ρ g) (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    rw [hρ, modAct_mk, mk_eq_mk_iff, MulAut.conjNormal_apply] at h1
    have h2 := hDn.conj_mem _ (inv_mem h1) x
    convert h2 using 1
    group
  obtain ⟨n, hn, ψ', hψ', k, θ, hθ⟩ := h25 (ModPD (oTwo Λ) Dd) hV2 _ _ _ _ Z₀
    (isL24Sz_image h hc hR hX hC) (h.isPGroup_T.map ρ) (map_mono h.T_le_normalizer)
    (CFSG.RankThree.S4Free.isElemAbelian_map h.elemAb ρ) hquad hZA hstab hgen hfix
    (oTwo_range_eq_bot h hc hR hX hC)
  have hinj : ψ'.ker = ⊥ := by
    obtain ⟨e⟩ := nonempty_range_mulEquiv h hc hR hX hC
    obtain ⟨-, -, hs⟩ := CFSG.LieType.Ree.suzuki_simple h.one_le h.card_K
    haveI := hs
    haveI : IsSimpleGroup ↥ρ.range := e.isSimpleGroup
    rcases (MonoidHom.normal_ker ψ').eq_bot_or_eq_top with h1 | h1
    · exact h1
    · exfalso
      haveI := nontrivial_sz n
      obtain ⟨y, hy⟩ := exists_ne (1 : CFSG.Open.Sz n)
      obtain ⟨x, rfl⟩ := hψ' y
      exact hy (MonoidHom.mem_ker.mp (h1 ▸ mem_top x))
  refine ⟨n, hn, ψ'.comp ρ.rangeRestrict, hψ'.comp ρ.rangeRestrict_surjective, ?_,
    Multiplicative (Fin k → Fin 4 → CFSG.RankThree.GF2n.SzExplicit.F n), inferInstance,
    θ.toMonoidHom.comp (QuotientGroup.mk' (Dd.subgroupOf (oTwo Λ))),
    (MulAut.congr θ).toMonoidHom.comp ρ, ?_, ?_, ?_, k, MulEquiv.refl _, ?_⟩
  · rw [← MonoidHom.comap_ker, hinj, MonoidHom.comap_bot, MonoidHom.ker_rangeRestrict, hker]
  · exact θ.surjective.comp (QuotientGroup.mk'_surjective _)
  · intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_subgroupOf] at hx
    rw [mem_subgroupOf, mem_center_iff]
    intro g
    exact (mem_centralizer_iff.mp (hc.L_le_centralizer_D (mem_top g)) _ hx).symm
  · intro g x y hxy
    show θ ((modAct (P := oTwo Λ) (D := Dd) g) (θ.symm (θ (x : ModPD (oTwo Λ) Dd)))) =
      θ (y : ModPD (oTwo Λ) Dd)
    rw [MulEquiv.symm_apply_apply, modAct_mk]
    congr 2
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, hxy]
  · intro g y
    have := hθ (ρ.rangeRestrict g) (θ.symm y)
    rw [MulEquiv.apply_symm_apply] at this
    simpa [MulAut.congr_apply] using this

end SzCfg

end CFSG.RankThree.S4Free.Stell34
