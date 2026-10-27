module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec64DirectCoord
public import CFSG.RankThree.GF2n.Stroth80.HeringSec65NMain

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

namespace HS6

section Core

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem Env.sl2_of_cent (I : Inputs) (e : Env hc n t m X)
    (h63b : StronglyClosedMod M (hc.CN t) (LB M Q B))
    (hD : ∀ g ∈ M, ∀ a ∈ hc.CN t, ∀ x ∈ X, ⁅x, g * a * g⁻¹⁆ ∈ Q) :
    QuotSat (Lgen M (hc.CN t)) Q (IsSLModel 2 (Nat.card Z)) := by
  classical
  have ht := e.hs.toSec5.mem
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hNM : hc.CN t ≤ M := e.CN_le_M
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN ht
  have hMconj : ∀ g ∈ M, conjSubgroup g M = M := fun g hg => hc.conj_M_eq hg
  have hQS : Q ≤ Lgen M (hc.CN t) := hQN.trans (le_Lgen_self M (hc.CN t))
  have hSM : Lgen M (hc.CN t) ≤ M := Lgen_le_M' hNM hMconj
  obtain ⟨g₀, hg₀M, hne⟩ := e.exists_conj_ne I
  obtain ⟨ι, _, _, K, _, _, _, Q', X', E, φ, _, ψ, u, hK, hX, hgeom, hmod⟩ :=
    e.exists_model_scalar I
  obtain ⟨Φ, a, hΦ, hsnd0, hfst0⟩ := hmod.exists_chart I e h63b hgeom hK hX hD hg₀M hne
  haveI : Nonempty ι := by
    have h1 := hgeom.dim
    rw [Module.finrank_fintype_fun_eq_card] at h1
    exact Fintype.card_pos_iff.mp (by have := e.hm; omega)
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hV'Q : conjSubgroup g₀ (Vt M (LB M Q B) B Z t) ≤ Q := by
    intro y hy
    have h1 := hVQ (mem_conjSubgroup.mp hy)
    have := (hc.conj_mem_Q_of_mem_M hg₀M).1 _ h1
    rwa [show g₀ * (g₀⁻¹ * y * g₀) * g₀⁻¹ = y by group] at this
  obtain ⟨C, hCmem⟩ := exists_Cgrp hc X
  have hCM : ∀ h ∈ C, h ∈ M := fun h hh => ((hCmem h).mp hh).1.1
  have hCQ : ∀ h ∈ C, ∀ y ∈ Q, h * y * h⁻¹ ∈ Q := fun h hh y hy =>
    (hc.conj_mem_Q_of_mem_M (hCM h hh)).1 y hy
  have hCZ : ∀ h ∈ C, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z := fun h hh z hz =>
    conj_Z_mem hc (hCM h hh) hz
  have hCX : ∀ h ∈ C, ∀ x ∈ X, ⁅h, x⁆ ∈ Q := fun h hh x hx => ((hCmem h).mp hh).2 x hx
  obtain ⟨ρ, hρ⟩ := exists_rep hΦ C hCQ hCZ hCX
  have hQC : Q ≤ C := by
    intro q hq
    refine (hCmem q).mpr ⟨hc.Q_le_H0 hq, fun x hx => ?_⟩
    have hxM := e.X_le_M hx
    have e1 : ⁅q, x⁆ = q * (x * q * x⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e1]
    exact Q.mul_mem hq (Q.inv_mem ((hc.conj_mem_Q_of_mem_M hxM).1 q hq))
  have hNC : ∀ g ∈ M, ∀ a ∈ hc.CN t, g * a * g⁻¹ ∈ C := by
    intro g hg a ha
    refine (hCmem _).mpr ⟨hc.conj_mem_H0 hg (e.CN_le_H0 I ha), fun x hx => ?_⟩
    have := Q.inv_mem (hD g hg a ha x hx)
    rwa [commutatorElement_inv] at this
  have hNC1 : ∀ a ∈ hc.CN t, a ∈ C := fun a ha => by simpa using hNC 1 M.one_mem a ha
  have hTC : ∀ y ∈ conjSubgroup g₀ (hc.CN t), y ∈ C := by
    intro y hy
    have := hNC g₀ hg₀M _ (mem_conjSubgroup.mp hy)
    rwa [show g₀ * (g₀⁻¹ * y * g₀) * g₀⁻¹ = y by group] at this
  have hSC : Lgen M (hc.CN t) ≤ C := by
    refine iSup₂_le fun g hg => ?_
    intro y hy
    have := hNC g hg _ (mem_conjSubgroup.mp hy)
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this
  have hker1 : ∀ (h : C), ρ h = 1 ↔ (h : G) ∈ Q := by
    intro h
    constructor
    · intro h1
      exact hc.hyp.centralizer_Qt _ (hCM h h.2)
        (comm_mem_Z_of_rho_one hΦ C ρ hρ hCQ h h1)
    · exact rho_eq_one_of_mem_Q hΦ C ρ hρ h
  let δ : C →* K := Matrix.detMonoidHom.comp ρ
  have hdetgen : ∀ g ∈ M, ∀ (y : G) (hyC : y ∈ C), g⁻¹ * y * g ∈ hc.CN t →
      (ρ ⟨y, hyC⟩).det = 1 := by
    intro g hg y hyC hyN
    have hyy : y * y ∈ Q := by
      have h1 : (g⁻¹ * y * g) * (g⁻¹ * y * g) ∈ Q := by
        have := (e.N_mod_Q I.h34).2 _ hyN
        rwa [pow_two] at this
      have := (hc.conj_mem_Q_of_mem_M hg).1 _ h1
      rwa [show g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ = y * y by group] at this
    have hsq : ρ ⟨y, hyC⟩ * ρ ⟨y, hyC⟩ = 1 := by
      rw [← map_mul]
      exact (hker1 _).mpr hyy
    have hd : (ρ ⟨y, hyC⟩).det * (ρ ⟨y, hyC⟩).det = 1 := by
      rw [← Matrix.det_mul, hsq, Matrix.det_one]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h3 : ((ρ ⟨y, hyC⟩).det - 1) ^ 2 = 0 := by
      linear_combination hd + (1 - (ρ ⟨y, hyC⟩).det) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h3)
  have hSK : Lgen M (hc.CN t) ≤ (MonoidHom.ker δ).map C.subtype := by
    refine iSup₂_le fun g hg => ?_
    intro y hy
    have hyN := mem_conjSubgroup.mp hy
    have hyC : y ∈ C := by
      have := hNC g hg _ hyN
      rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this
    exact ⟨⟨y, hyC⟩, MonoidHom.mem_ker.mpr (hdetgen g hg y hyC hyN), rfl⟩
  have hdet : ∀ s : ↥(Lgen M (hc.CN t)), (ρ ⟨(s : G), hSC s.2⟩).det = 1 := by
    intro s
    obtain ⟨c, hc1, hcs⟩ := hSK s.2
    have : (⟨(s : G), hSC s.2⟩ : C) = c := Subtype.ext hcs.symm
    rw [this]
    exact MonoidHom.mem_ker.mp hc1
  let ρS : ↥(Lgen M (hc.CN t)) →* Matrix.SpecialLinearGroup (Fin 2) K :=
    { toFun := fun s => ⟨ρ ⟨(s : G), hSC s.2⟩, hdet s⟩
      map_one' := Subtype.ext (by
        have : (⟨((1 : ↥(Lgen M (hc.CN t))) : G), hSC (1 : ↥(Lgen M (hc.CN t))).2⟩ : C) = 1 :=
          Subtype.ext rfl
        show ρ ⟨((1 : ↥(Lgen M (hc.CN t))) : G), _⟩ = 1
        rw [this, map_one])
      map_mul' := fun s s' => Subtype.ext (by
        have : (⟨((s * s' : ↥(Lgen M (hc.CN t))) : G), hSC (s * s').2⟩ : C) =
            ⟨(s : G), hSC s.2⟩ * ⟨(s' : G), hSC s'.2⟩ := Subtype.ext rfl
        show ρ ⟨((s * s' : ↥(Lgen M (hc.CN t))) : G), _⟩ = ρ _ * ρ _
        rw [this, map_mul]) }
  have hkerS : ρS.ker = Q.subgroupOf (Lgen M (hc.CN t)) := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      exact (hker1 ⟨(s : G), hSC s.2⟩).mp (congrArg Subtype.val h1)
    · intro h1
      exact Subtype.ext ((hker1 ⟨(s : G), hSC s.2⟩).mpr h1)
  have hVQ' : Vt M (LB M Q B) B Z t ≤ Q := hVQ
  have hupper : ∀ (a : G) (ha : a ∈ hc.CN t), ρ ⟨a, hNC1 a ha⟩ 0 0 = 1 ∧
      ρ ⟨a, hNC1 a ha⟩ 1 0 = 0 ∧ ρ ⟨a, hNC1 a ha⟩ 1 1 = 1 := fun a ha =>
    rho_upper hΦ hVQ' hsnd0 C ρ hρ ⟨a, hNC1 a ha⟩ (Ctx.mem_CN.mp ha).2
      (fun y hy => e.comm_mem_V I.h34 ha hy)
  have hlower : ∀ (y : G) (hy : y ∈ conjSubgroup g₀ (hc.CN t)), ρ ⟨y, hTC y hy⟩ 0 0 = 1 ∧
      ρ ⟨y, hTC y hy⟩ 0 1 = 0 ∧ ρ ⟨y, hTC y hy⟩ 1 1 = 1 := by
    intro y hy
    have hyN := mem_conjSubgroup.mp hy
    have hya : y = g₀ * (g₀⁻¹ * y * g₀) * g₀⁻¹ := by group
    refine rho_lower hΦ hV'Q hfst0 C ρ hρ ⟨y, hTC y hy⟩ (fun v hv => ?_) (fun x hx => ?_)
    · show ⁅y, v⁆ ∈ Z
      rw [hya]
      exact e.comm_conj_CN_mem_Z hg₀M hyN hv
    · show ⁅y, x⁆ ∈ _
      rw [hya]
      exact e.comm_conj_CN_mem_V' I hg₀M hyN hx
  have hmatN : ∀ (a : G) (ha : a ∈ hc.CN t), ρ ⟨a, hNC1 a ha⟩ 0 1 = 0 →
      ρ ⟨a, hNC1 a ha⟩ = 1 := by
    intro a ha h01
    obtain ⟨h00, h10, h11⟩ := hupper a ha
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11, h01]
  have hmatT : ∀ (y : G) (hy : y ∈ conjSubgroup g₀ (hc.CN t)), ρ ⟨y, hTC y hy⟩ 1 0 = 0 →
      ρ ⟨y, hTC y hy⟩ = 1 := by
    intro y hy h10
    obtain ⟨h00, h01, h11⟩ := hlower y hy
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11, h01]
  have hQT : Q ≤ conjSubgroup g₀ (hc.CN t) := by
    intro q hq
    have : g₀⁻¹ * q * g₀ ∈ Q := (hc.conj_mem_Q_of_mem_M hg₀M).2 q hq
    exact mem_conjSubgroup.mpr (hQN this)
  let fN : ↥(hc.CN t) →* Multiplicative K :=
    { toFun := fun a => Multiplicative.ofAdd (ρ ⟨(a : G), hNC1 a a.2⟩ 0 1)
      map_one' := by
        have : (⟨((1 : ↥(hc.CN t)) : G), hNC1 _ (1 : ↥(hc.CN t)).2⟩ : C) = 1 := Subtype.ext rfl
        show Multiplicative.ofAdd (ρ ⟨((1 : ↥(hc.CN t)) : G), _⟩ 0 1) = 1
        rw [this, map_one]
        simp
      map_mul' := fun a b => by
        have hab : (⟨((a * b : ↥(hc.CN t)) : G), hNC1 _ (a * b).2⟩ : C) =
            ⟨(a : G), hNC1 _ a.2⟩ * ⟨(b : G), hNC1 _ b.2⟩ := Subtype.ext rfl
        show Multiplicative.ofAdd (ρ ⟨((a * b : ↥(hc.CN t)) : G), _⟩ 0 1) =
          Multiplicative.ofAdd (ρ _ 0 1) * Multiplicative.ofAdd (ρ _ 0 1)
        rw [hab, map_mul, Matrix.mul_apply, Fin.sum_univ_two, (hupper _ a.2).1,
          (hupper _ b.2).2.2, ← ofAdd_add, one_mul, mul_one, add_comm] }
  have hsurjN := surj_of_ker hQN fN (fun a => by
      show Multiplicative.ofAdd (ρ ⟨(a : G), hNC1 a a.2⟩ 0 1) = 1 ↔ _
      rw [ofAdd_eq_one]
      constructor
      · intro h01
        exact (hker1 ⟨(a : G), hNC1 a a.2⟩).mp (hmatN _ a.2 h01)
      · intro hq
        have := (hker1 ⟨(a : G), hNC1 a a.2⟩).mpr hq
        rw [this]
        simp)
    (by rw [e.hs.cardN, hK])
  let fT : ↥(conjSubgroup g₀ (hc.CN t)) →* Multiplicative K :=
    { toFun := fun y => Multiplicative.ofAdd (ρ ⟨(y : G), hTC y y.2⟩ 1 0)
      map_one' := by
        have : (⟨((1 : ↥(conjSubgroup g₀ (hc.CN t))) : G),
            hTC _ (1 : ↥(conjSubgroup g₀ (hc.CN t))).2⟩ : C) = 1 := Subtype.ext rfl
        show Multiplicative.ofAdd (ρ ⟨((1 : ↥(conjSubgroup g₀ (hc.CN t))) : G), _⟩ 1 0) = 1
        rw [this, map_one]
        simp
      map_mul' := fun a b => by
        have hab : (⟨((a * b : ↥(conjSubgroup g₀ (hc.CN t))) : G), hTC _ (a * b).2⟩ : C) =
            ⟨(a : G), hTC _ a.2⟩ * ⟨(b : G), hTC _ b.2⟩ := Subtype.ext rfl
        show Multiplicative.ofAdd (ρ ⟨((a * b : ↥(conjSubgroup g₀ (hc.CN t))) : G), _⟩ 1 0) =
          Multiplicative.ofAdd (ρ _ 1 0) * Multiplicative.ofAdd (ρ _ 1 0)
        rw [hab, map_mul, Matrix.mul_apply, Fin.sum_univ_two, (hlower _ b.2).1,
          (hlower _ a.2).2.2, ← ofAdd_add, mul_one, one_mul] }
  have hsurjT := surj_of_ker hQT fT (fun y => by
      show Multiplicative.ofAdd (ρ ⟨(y : G), hTC y y.2⟩ 1 0) = 1 ↔ _
      rw [ofAdd_eq_one]
      constructor
      · intro h10
        exact (hker1 ⟨(y : G), hTC y y.2⟩).mp (hmatT _ y.2 h10)
      · intro hq
        have := (hker1 ⟨(y : G), hTC y y.2⟩).mpr hq
        rw [this]
        simp)
    (by rw [card_conjSubgroup, e.hs.cardN, hK])
  have hsurj : Function.Surjective ρS := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← SL2Grp.sl2Upper_sup_Lower K]
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨lam, rfl⟩ := CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup.mp hg
      obtain ⟨a, ha⟩ := hsurjN lam
      refine ⟨⟨(a : G), le_Lgen_self M _ a.2⟩, Subtype.ext ?_⟩
      have h01 : ρ ⟨(a : G), hNC1 a a.2⟩ 0 1 = lam := by
        have := congrArg Multiplicative.toAdd ha
        simpa [fN] using this
      obtain ⟨h00, h10, h11⟩ := hupper a a.2
      show ρ ⟨(a : G), hSC (le_Lgen_self M _ a.2)⟩ = ((Matrix.SpecialLinearGroup.transvection
        SL2Grp.sl2Idx01 lam : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      rw [SL2Grp.sl2_coe_t01]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h10, h11, h01]
    · obtain ⟨lam, rfl⟩ := CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup.mp hg
      obtain ⟨y, hy⟩ := hsurjT lam
      have hyS : (y : G) ∈ Lgen M (hc.CN t) :=
        (le_iSup₂ (f := fun m' (_ : m' ∈ M) => conjSubgroup m' (hc.CN t)) g₀ hg₀M) y.2
      refine ⟨⟨(y : G), hyS⟩, Subtype.ext ?_⟩
      have h10 : ρ ⟨(y : G), hTC y y.2⟩ 1 0 = lam := by
        have := congrArg Multiplicative.toAdd hy
        simpa [fT] using this
      obtain ⟨h00, h01, h11⟩ := hlower y y.2
      show ρ ⟨(y : G), hSC hyS⟩ = ((Matrix.SpecialLinearGroup.transvection
        SL2Grp.sl2Idx10 lam : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      rw [SL2Grp.sl2_coe_t10]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h10, h11, h01]
  haveI hNorm : (Q.subgroupOf (Lgen M (hc.CN t))).Normal := by
    rw [← hkerS]
    exact MonoidHom.normal_ker ρS
  exact ⟨hNorm, K, inferInstance, inferInstance, hK, ⟨((QuotientGroup.quotientMulEquivOfEq
    hkerS.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ρS hsurj)).trans
    (specialLinearGroupEquivStatedSL 2 K)⟩⟩

end Core

end HS6

end CFSG.RankThree.GF2n.Stroth80
