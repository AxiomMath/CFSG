module

public import CFSG.RankThree.GF2n.Stroth80.Sec717OrbitOdd
public import CFSG.RankThree.GF2n.Stroth80.Sec717LNaturalOrbit
public import CFSG.RankThree.GF2n.Stroth80.Sec717InvProof
public import CFSG.ClassicalGroups.SpecialLinear.VectorStabilizer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.SpecialLinear
open scoped commutatorElement

section SecAct

variable {G : Type} [Group G]

@[expose] noncomputable def sec717SecConj (R A B : Subgroup G) [(B.subgroupOf A).Normal]
    (hRA : ∀ r ∈ R, ∀ a ∈ A, r * a * r⁻¹ ∈ A) (hRB : ∀ r ∈ R, ∀ b ∈ B, r * b * r⁻¹ ∈ B)
    (r : ↥R) : MulAut (↥A ⧸ B.subgroupOf A) :=
  QuotientGroup.congr (B.subgroupOf A) (B.subgroupOf A)
    (sec717ConjA A (r : G) (hRA r r.2) fun a ha => by
      simpa using hRA (r : G)⁻¹ (R.inv_mem r.2) a ha)
    (by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Subgroup.mem_subgroupOf] at hy ⊢
        exact hRB r r.2 _ hy
      · intro hx
        refine ⟨⟨(r : G)⁻¹ * x * r, by simpa using hRA (r : G)⁻¹ (R.inv_mem r.2) x x.2⟩, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          simpa using hRB (r : G)⁻¹ (R.inv_mem r.2) x (Subgroup.mem_subgroupOf.mp hx)
        · apply Subtype.ext
          show (r : G) * ((r : G)⁻¹ * x * r) * (r : G)⁻¹ = x
          group)

theorem sec717SecConj_mk (R A B : Subgroup G) [(B.subgroupOf A).Normal]
    (hRA : ∀ r ∈ R, ∀ a ∈ A, r * a * r⁻¹ ∈ A) (hRB : ∀ r ∈ R, ∀ b ∈ B, r * b * r⁻¹ ∈ B)
    (r : ↥R) (a : ↥A) :
    sec717SecConj R A B hRA hRB r (QuotientGroup.mk a) =
      QuotientGroup.mk ⟨(r : G) * a * (r : G)⁻¹, hRA r r.2 a a.2⟩ := rfl

@[expose] noncomputable def sec717SecAct (R A B : Subgroup G) [(B.subgroupOf A).Normal]
    (hRA : ∀ r ∈ R, ∀ a ∈ A, r * a * r⁻¹ ∈ A) (hRB : ∀ r ∈ R, ∀ b ∈ B, r * b * r⁻¹ ∈ B) :
    ↥R →* MulAut (↥A ⧸ B.subgroupOf A) :=
  MonoidHom.mk' (sec717SecConj R A B hRA hRB) fun r s => by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [MulAut.mul_apply, sec717SecConj_mk, sec717SecConj_mk, sec717SecConj_mk]
      congr 1
      apply Subtype.ext
      show ((r * s : ↥R) : G) * a * ((r * s : ↥R) : G)⁻¹ =
        (r : G) * ((s : G) * a * (s : G)⁻¹) * (r : G)⁻¹
      rw [Subgroup.coe_mul]
      group

theorem sec717SecAct_mk (R A B : Subgroup G) [(B.subgroupOf A).Normal]
    (hRA : ∀ r ∈ R, ∀ a ∈ A, r * a * r⁻¹ ∈ A) (hRB : ∀ r ∈ R, ∀ b ∈ B, r * b * r⁻¹ ∈ B)
    (r : ↥R) (a : ↥A) :
    sec717SecAct R A B hRA hRB r (QuotientGroup.mk a) =
      QuotientGroup.mk ⟨(r : G) * a * (r : G)⁻¹, hRA r r.2 a a.2⟩ := rfl

end SecAct


theorem sec717OrbitOdd_of_typing (hCN : Sec7CommNStatement) (hTyp : Sec717LTypingStatement) :
    Sec717OrbitOddStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn y hy hyV
  classical
  have hp3c := hp3
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0L : Z0 ≤ L := hL.2.2.2.2.2
  have hQL : Q ≤ L := hL.1
  have hLCN : L ≤ hc.CN t := hL.2.1
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hLR : L ≤ Rt M (LB M Q B) t := hLCN.trans hCNR
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQR : Q ≤ Rt M (LB M Q B) t := hQZ0.trans hZ0.le
  have hQCN : Q ≤ hc.CN t := hQL.trans hLCN
  have hQn : ∀ g ∈ M, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) x).mp hx
  have hRL : ∀ r ∈ Rt M (LB M Q B) t, ∀ a ∈ L, r * a * r⁻¹ ∈ L := fun r hr a ha =>
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp (hL.2.2.2.1 r hr)) a).mp ha
  have hRZ0 : ∀ r ∈ Rt M (LB M Q B) t, ∀ z ∈ Z0, r * z * r⁻¹ ∈ Z0 := fun r hr z hz =>
    (Subgroup.mem_normalizer_iff.mp
      (hZ0.mem_normalizer (fun ρ hρ x hx => hQn ρ (hRM hρ) x hx) hr) z).mp hz
  haveI hZ0n : (Z0.subgroupOf L).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hRZ0 g (hLR g.2) x hx⟩
  have hXcomm : ∀ a b : ↥L ⧸ Z0.subgroupOf L, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have key : ((a : G) * b)⁻¹ * ((b : G) * a) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [key]
    exact hQZ0 (hL.2.2.2.2.1 _ (L.inv_mem b.2) _ (L.inv_mem a.2))
  letI : CommGroup (↥L ⧸ Z0.subgroupOf L) := sec717CommGroup hXcomm
  haveI hQn0 : (Q.subgroupOf Z0).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hQn g (hRM (hZ0.le g.2)) x hx⟩
  have hYcomm : ∀ a b : ↥Z0 ⧸ Q.subgroupOf Z0, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have key : ((a : G) * b)⁻¹ * ((b : G) * a) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [key]
    exact hZ0.comm_mem (Z0.inv_mem b.2) (hZ0.le (Z0.inv_mem a.2))
  letI : CommGroup (↥Z0 ⧸ Q.subgroupOf Z0) := sec717CommGroup hYcomm
  set ρ := sec717SecAct (Rt M (LB M Q B) t) L Z0 hRL hRZ0 with hρ
  obtain ⟨K, hKf, hKfin, hKZ, φ₀, hφr, hker, -⟩ := hp3
  obtain ⟨n0, -, hZn0, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := sec717_charP_two (n := n0) (by rw [hKZ, hZn0])
  have hmemN : ∀ h : ↥(Rt M (LB M Q B) t), φ₀ h = 1 ↔ (h : G) ∈ hc.CN t := by
    intro h
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hkerρ : ∀ h : ↥(Rt M (LB M Q B) t), φ₀ h = 1 → ρ h = 1 := by
    intro h hh
    have hmem : (h : G) ∈ hc.CN t := (hmemN h).mp hh
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
    rw [hρ, sec717SecAct_mk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((h : G) * a * (h : G)⁻¹)⁻¹ * a ∈ Z0
    have hid : ((h : G) * a * (h : G)⁻¹)⁻¹ * a = ⁅(h : G), (a : G)⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [hid]
    exact hCN G M Q Z B hc n t hs Z0 hZ0
      (Subgroup.commutator_mem_commutator hmem (hLCN (L.inv_mem a.2)))
  obtain ⟨η, ψ, hηs, hηk, hψ'⟩ := sec717L_naturalModule_of hTyp hc hs hp3c hZ0 hZ0N hTI hL hLn
    hXcomm hKZ φ₀ hmemN
  have hψ : ∀ (h : ↥(Rt M (LB M Q B) t)) (x : ↥L ⧸ Z0.subgroupOf L),
      ψ (Additive.ofMul (ρ h x)) = η h • ψ (Additive.ofMul x) := by
    intro h x
    induction x using QuotientGroup.induction_on with
    | H a =>
      rw [hρ, sec717SecAct_mk]
      exact hψ' h a _
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (y : Mbar M Q)
  have hy₀L : (y₀ : G) ∈ L := by
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) y₀ ∈ bar M Q L := by
      rw [hy₀]
      exact Subgroup.mem_subgroupOf.mp hy
    exact (mk_mem_bar_iff_sec4 hQL y₀).mp h1
  have hy₀Z : (y₀ : G) ∉ Z0 := by
    intro h
    apply hyV
    rw [Subgroup.mem_subgroupOf, ← hy₀]
    exact (mk_mem_bar_iff_sec4 hQZ0 y₀).mpr h
  set x : ↥L ⧸ Z0.subgroupOf L := QuotientGroup.mk (⟨y₀, hy₀L⟩ : ↥L) with hxdef
  have hx : x ≠ 1 := by
    intro h
    rw [hxdef, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact hy₀Z h
  set Sx := (MulAction.stabilizer (MulAut (↥L ⧸ Z0.subgroupOf L)) x).comap ρ with hSx
  have hmemSx : ∀ r : ↥(Rt M (LB M Q B) t),
      r ∈ Sx ↔ ((r : G) * y₀ * (r : G)⁻¹)⁻¹ * y₀ ∈ Z0 := by
    intro r
    rw [hSx, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def, hxdef, hρ,
      sec717SecAct_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hπmem : ∀ r : ↥(Rt M (LB M Q B) t),
      QuotientGroup.mk' (Q.subgroupOf M) (⟨r, hRM r.2⟩ : ↥M) ∈ bar M Q (H0 M Z) := fun r =>
    (mk_mem_bar_iff_sec4 hQH _).mpr (hRH r.2)
  let π : ↥(Rt M (LB M Q B) t) →*
      ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) :=
    { toFun := fun r => ⟨⟨_, hπmem r⟩, Subgroup.mem_subgroupOf.mpr
        ((mk_mem_bar_iff_sec4 hQR _).mpr r.2)⟩
      map_one' := Subtype.ext (Subtype.ext (map_one _))
      map_mul' := fun r s => Subtype.ext (Subtype.ext (map_mul (QuotientGroup.mk' (Q.subgroupOf M))
        (⟨r, hRM r.2⟩ : ↥M) ⟨s, hRM s.2⟩)) }
  have hπval : ∀ r : ↥(Rt M (LB M Q B) t),
      ((π r : ↥(bar M Q (H0 M Z))) : Mbar M Q) =
        QuotientGroup.mk' (Q.subgroupOf M) (⟨r, hRM r.2⟩ : ↥M) := fun r => rfl
  have hπs : Function.Surjective π := by
    rintro ⟨⟨w, hwH⟩, hwR⟩
    obtain ⟨m, hm, hmw⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hwR)
    refine ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [hπval]
    exact hmw
  have hNR : (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) := by
    intro w hw
    exact Subgroup.mem_subgroupOf.mpr (bar_mono' hCNR (Subgroup.mem_subgroupOf.mp hw))
  have hcomapN : ((((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
      ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))).comap π) =
        (hc.CN t).subgroupOf (Rt M (LB M Q B) t) := by
    ext r
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, hπval]
    exact mk_mem_bar_iff_sec4 hQCN _
  have hy₀R : (y₀ : G) ∈ Rt M (LB M Q B) t := hLR hy₀L
  have hmemSx' : ∀ r : ↥(Rt M (LB M Q B) t),
      r ∈ Sx ↔ (r : G) * y₀ * (r : G)⁻¹ * (y₀ : G)⁻¹ ∈ Z0 := by
    intro r
    rw [hmemSx]
    have e : ((r : G) * y₀ * (r : G)⁻¹)⁻¹ * y₀ =
        (y₀ : G)⁻¹ * ((r : G) * y₀ * (r : G)⁻¹ * (y₀ : G)⁻¹)⁻¹ * (y₀ : G)⁻¹⁻¹ := by group
    rw [e]
    constructor
    · intro h
      have h1 := hRZ0 _ hy₀R _ h
      have e2 : (y₀ : G) * ((y₀ : G)⁻¹ * ((r : G) * y₀ * (r : G)⁻¹ * (y₀ : G)⁻¹)⁻¹ *
          (y₀ : G)⁻¹⁻¹) * (y₀ : G)⁻¹ = ((r : G) * y₀ * (r : G)⁻¹ * (y₀ : G)⁻¹)⁻¹ := by group
      rw [e2] at h1
      simpa using Z0.inv_mem h1
    · intro h
      exact hRZ0 _ (Subgroup.inv_mem _ hy₀R) _ (Z0.inv_mem h)
  set T := ((((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) ⊓
      Subgroup.centralizer ({y} : Set ↥(bar M Q (H0 M Z)))).subgroupOf
      ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))).comap π) with hT
  have hmemT : ∀ r : ↥(Rt M (LB M Q B) t),
      r ∈ T ↔ (r : G) * y₀ * (r : G)⁻¹ * (y₀ : G)⁻¹ ∈ Q := by
    intro r
    rw [hT, Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    have hRmem : ((π r : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))) :
        ↥(bar M Q (H0 M Z))) ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) :=
      (π r).2
    simp only [hRmem, true_and]
    have hyval : ((y : ↥(bar M Q (H0 M Z))) : Mbar M Q) =
        QuotientGroup.mk' (Q.subgroupOf M) y₀ := hy₀.symm
    rw [← Subtype.coe_inj, Subgroup.coe_mul, Subgroup.coe_mul, hπval, hyval, ← map_mul, ← map_mul,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hrM : (r : G) ∈ M := hRM r.2
    have hy₀M : (y₀ : G) ∈ M := y₀.2
    constructor
    · intro h
      have h1 := hQn _ (M.mul_mem hrM hy₀M) _ (Q.inv_mem h)
      have e : (r : G) * y₀ * ((((r : G) * y₀)⁻¹ * ((y₀ : G) * r))⁻¹) * ((r : G) * y₀)⁻¹ =
          (r : G) * y₀ * (r : G)⁻¹ * (y₀ : G)⁻¹ := by group
      rwa [e] at h1
    · intro h
      have h1 := hQn _ (M.inv_mem (M.mul_mem hrM hy₀M)) _ (Q.inv_mem h)
      have e : ((r : G) * y₀)⁻¹ * ((r : G) * y₀ * (r : G)⁻¹ * (y₀ : G)⁻¹)⁻¹ *
          ((r : G) * y₀)⁻¹⁻¹ = ((r : G) * y₀)⁻¹ * ((y₀ : G) * r) := by group
      rwa [e] at h1
  have hW : ((((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) ⊓
      Subgroup.centralizer ({y} : Set ↥(bar M Q (H0 M Z)))) ⊔
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
      ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))).comap π =
        T ⊔ (hc.CN t).subgroupOf (Rt M (LB M Q B) t) := by
    rw [Subgroup.subgroupOf_sup inf_le_left hNR, ← Subgroup.comap_sup_eq π _ _ hπs, hcomapN]
  have hNSx : (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ≤ Sx := by
    intro r hr
    have h1 : ρ r = 1 := hkerρ r ((hmemN r).mpr (Subgroup.mem_subgroupOf.mp hr))
    rw [hSx, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, h1, one_smul]
  have hTSx : T ≤ Sx := fun r hr => (hmemSx' r).mpr (hQZ0 ((hmemT r).mp hr))
  have hcZ : ∀ s : ↥Sx, ((s : ↥(Rt M (LB M Q B) t)) : G) * y₀ *
      ((s : ↥(Rt M (LB M Q B) t)) : G)⁻¹ * (y₀ : G)⁻¹ ∈ Z0 := fun s => (hmemSx' s).mp s.2
  let θf : ↥Sx → ↥Z0 ⧸ Q.subgroupOf Z0 := fun s => QuotientGroup.mk ⟨_, hcZ s⟩
  have hθmul : ∀ s₁ s₂ : ↥Sx, θf (s₁ * s₂) = θf s₁ * θf s₂ := by
    intro s₁ s₂
    set a : G := ((s₁ : ↥(Rt M (LB M Q B) t)) : G) with ha
    set b : G := ((s₂ : ↥(Rt M (LB M Q B) t)) : G) with hb
    have haR : a ∈ Rt M (LB M Q B) t := (s₁ : ↥(Rt M (LB M Q B) t)).2
    have hcb : b * y₀ * b⁻¹ * (y₀ : G)⁻¹ ∈ Z0 := hcZ s₂
    have hconj : a * (b * y₀ * b⁻¹ * (y₀ : G)⁻¹) * a⁻¹ ∈ Z0 := hRZ0 a haR _ hcb
    have e : (((s₁ * s₂ : ↥Sx) : ↥(Rt M (LB M Q B) t)) : G) * y₀ *
        (((s₁ * s₂ : ↥Sx) : ↥(Rt M (LB M Q B) t)) : G)⁻¹ * (y₀ : G)⁻¹ =
          (a * (b * y₀ * b⁻¹ * (y₀ : G)⁻¹) * a⁻¹) * (a * y₀ * a⁻¹ * (y₀ : G)⁻¹) := by
      simp only [Subgroup.coe_mul, ha, hb]
      group
    have h1 : θf (s₁ * s₂) = (QuotientGroup.mk (⟨_, hconj⟩ : ↥Z0) : ↥Z0 ⧸ Q.subgroupOf Z0) *
        QuotientGroup.mk (⟨_, hcZ s₁⟩ : ↥Z0) := by
      rw [← QuotientGroup.mk_mul]
      show (QuotientGroup.mk (⟨_, hcZ (s₁ * s₂)⟩ : ↥Z0) : ↥Z0 ⧸ Q.subgroupOf Z0) =
        QuotientGroup.mk ((⟨_, hconj⟩ : ↥Z0) * ⟨_, hcZ s₁⟩)
      congr 1
      apply Subtype.ext
      exact e
    have h2 : (QuotientGroup.mk (⟨_, hconj⟩ : ↥Z0) : ↥Z0 ⧸ Q.subgroupOf Z0) = θf s₂ := by
      show QuotientGroup.mk _ = QuotientGroup.mk _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show (a * (b * y₀ * b⁻¹ * (y₀ : G)⁻¹) * a⁻¹)⁻¹ * (b * y₀ * b⁻¹ * (y₀ : G)⁻¹) ∈ Q
      have h3 := hZ0.comm_mem (Z0.inv_mem hcb) haR
      have e3 : (a * (b * y₀ * b⁻¹ * (y₀ : G)⁻¹) * a⁻¹)⁻¹ * (b * y₀ * b⁻¹ * (y₀ : G)⁻¹) =
          ⁅(b * y₀ * b⁻¹ * (y₀ : G)⁻¹)⁻¹, a⁆⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e3]
      exact Q.inv_mem h3
    rw [h1, h2, mul_comm]
  let θ : ↥Sx →* ↥Z0 ⧸ Q.subgroupOf Z0 := MonoidHom.mk' θf hθmul
  have hSxeq : Sx = T ⊔ (hc.CN t).subgroupOf (Rt M (LB M Q B) t) := by
    refine le_antisymm (fun s hs => ?_) (sup_le hTSx hNSx)
    obtain ⟨k, hk1, hθk⟩ :=
      exists_mem_ker_eq_of_natural (n := 4) (A := ↥Z0 ⧸ Q.subgroupOf Z0) (by norm_num) hηs hψ hx
        θ ⟨s, hs⟩
    have hkN : (k : ↥(Rt M (LB M Q B) t)) ∈ (hc.CN t).subgroupOf (Rt M (LB M Q B) t) :=
      Subgroup.mem_subgroupOf.mpr ((hmemN _).mp ((hηk _).mp hk1))
    have hkT : (k : ↥(Rt M (LB M Q B) t))⁻¹ * s ∈ T := by
      have hθ1 : θ (k⁻¹ * ⟨s, hs⟩) = 1 := by
        rw [map_mul, map_inv, ← hθk, inv_mul_cancel]
      have h2 : ((k⁻¹ * ⟨s, hs⟩ : ↥Sx) : ↥(Rt M (LB M Q B) t)) = (k : ↥(Rt M (LB M Q B) t))⁻¹ * s :=
        rfl
      rw [hmemT, ← h2]
      have h3 := (QuotientGroup.eq_one_iff _).mp hθ1
      exact Subgroup.mem_subgroupOf.mp h3
    have e : s = (k : ↥(Rt M (LB M Q B) t)) * ((k : ↥(Rt M (LB M Q B) t))⁻¹ * s) := by group
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup hkN hkT
  rw [← Subgroup.index_comap_of_surjective _ hπs, hW, ← hSxeq, hSx,
    index_stabilizer_of_natural (by norm_num) hηs hψ hx]
  have hn0 : n0 ≠ 0 := by
    rintro rfl
    have := hc.hyp.q4
    rw [hZn0] at this
    norm_num at this
  have hq : Nat.card K = 2 ^ n0 := by rw [hKZ, hZn0]
  have heven : Even (Nat.card K ^ 4) := by
    rw [hq]
    exact Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hn0⟩, by norm_num⟩
  exact Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by rw [hq]; positivity)))
    heven odd_one

end CFSG.RankThree.GF2n.Stroth80
