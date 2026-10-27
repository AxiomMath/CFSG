module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaPlusLine
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4SlcProj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InComplement
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SemiregularBar
public import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

structure OmegaPlusTorus (c : Ctx23L D Ch) (r : ℕ) (a b t : G) : Prop where
  r_prime : r.Prime
  r_ne_two : r ≠ 2
  a_mem : a ∈ c.L
  b_mem : b ∈ c.L
  t_mem : t ∈ c.L
  a_order : orderOf a = r
  b_order : orderOf b = r
  commute : a * b = b * a
  a_centralizes : a ∈ Subgroup.centralizer (D.Z : Set G)
  b_mem_M : b ∈ D.M
  b_not_centralizes : b ∉ Subgroup.centralizer (D.Z : Set G)
  t_not_mem_M : t ∉ D.M
  t_order : ∃ k : ℕ, orderOf t = 2 ^ k
  t_inv_a : t * a * t⁻¹ = a⁻¹
  t_inv_b : t * b * t⁻¹ = b⁻¹
  permutes : Permutes (Subgroup.zpowers a) D.T

private theorem actTil_zpow_eq (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {a : G} (ha : a ∈ c.L)
    (n : ℤ) :
    actTil (⊥ : Subgroup G) c.V hV ⟨a ^ n, c.L_le_stabTil (c.L.zpow_mem ha n)⟩ =
      (c.phiL hV ⟨a, ha⟩ : MulAut (c.W hV)) ^ n := by
  have h1 : (⟨a ^ n, c.L_le_stabTil (c.L.zpow_mem ha n)⟩ :
      ↥(stabTil (⊥ : Subgroup G) c.V)) =
      (⟨a, c.L_le_stabTil ha⟩ : ↥(stabTil (⊥ : Subgroup G) c.V)) ^ n := by
    apply Subtype.ext
    simp
  rw [h1, map_zpow]
  rfl

private theorem actTil_inverter_eq_one (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {a s s' : G}
    (ha : a ∈ c.L) (hs : s ∈ D.T) (hs' : s' ∈ D.T) (i j : ℤ) (tstar beta : MulAut (c.W hV))
    (hs'eq : c.phiT hV ⟨s', hs'⟩ = tstar)
    (htbeta : tstar * beta =
      (c.phiL hV ⟨a, ha⟩ : MulAut (c.W hV)) ^ i * c.phiT hV ⟨s, hs⟩)
    (hbetaeq : beta = (c.phiL hV ⟨a, ha⟩ : MulAut (c.W hV)) ^ j)
    (hy_stab : (s'⁻¹ * a ^ i * s * (a ^ j)⁻¹ : G) ∈ stabTil (⊥ : Subgroup G) c.V) :
    actTil (⊥ : Subgroup G) c.V hV ⟨s'⁻¹ * a ^ i * s * (a ^ j)⁻¹, hy_stab⟩ = 1 := by
  have hyeq : (⟨s'⁻¹ * a ^ i * s * (a ^ j)⁻¹, hy_stab⟩ :
      ↥(stabTil (⊥ : Subgroup G) c.V)) =
      (⟨s', c.T_le_stabTil hs'⟩ : ↥(stabTil (⊥ : Subgroup G) c.V))⁻¹ *
        ⟨a ^ i, c.L_le_stabTil (c.L.zpow_mem ha i)⟩ *
        ⟨s, c.T_le_stabTil hs⟩ *
        (⟨a ^ j, c.L_le_stabTil (c.L.zpow_mem ha j)⟩ :
          ↥(stabTil (⊥ : Subgroup G) c.V))⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  rw [hyeq]
  simp only [map_mul, map_inv, actTil_zpow_eq c hV ha i, actTil_zpow_eq c hV ha j]
  rw [show actTil (⊥ : Subgroup G) c.V hV ⟨s', c.T_le_stabTil hs'⟩ = tstar from hs'eq,
    show actTil (⊥ : Subgroup G) c.V hV ⟨s, c.T_le_stabTil hs⟩ = c.phiT hV ⟨s, hs⟩ from rfl]
  have hre : tstar⁻¹ * (c.phiL hV ⟨a, ha⟩ : MulAut (c.W hV)) ^ i *
      c.phiT hV ⟨s, hs⟩ * beta⁻¹ =
      tstar⁻¹ * ((c.phiL hV ⟨a, ha⟩ : MulAut (c.W hV)) ^ i *
        c.phiT hV ⟨s, hs⟩) * beta⁻¹ := by group
  rw [← hbetaeq, hre, ← htbeta]
  group

private theorem mem_sup_stabTil_inverter (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {a s s' : G}
    (ha : a ∈ c.L) (hs : s ∈ D.T) (hs' : s' ∈ D.T) (i j : ℤ) :
    (s'⁻¹ * a ^ i * s * (a ^ j)⁻¹ : G) ∈ c.L ⊔ D.T ∧
      (s'⁻¹ * a ^ i * s * (a ^ j)⁻¹ : G) ∈ stabTil (⊥ : Subgroup G) c.V := by
  have hs'T : s' ∈ c.L ⊔ D.T := (le_sup_right : D.T ≤ c.L ⊔ D.T) hs'
  have haiT : a ^ i ∈ c.L ⊔ D.T := (le_sup_left : c.L ≤ c.L ⊔ D.T) (c.L.zpow_mem ha i)
  have hsT : s ∈ c.L ⊔ D.T := (le_sup_right : D.T ≤ c.L ⊔ D.T) hs
  have hajT : a ^ j ∈ c.L ⊔ D.T := (le_sup_left : c.L ≤ c.L ⊔ D.T) (c.L.zpow_mem ha j)
  have hyLT : s'⁻¹ * a ^ i * s * (a ^ j)⁻¹ ∈ c.L ⊔ D.T :=
    (c.L ⊔ D.T).mul_mem
      ((c.L ⊔ D.T).mul_mem ((c.L ⊔ D.T).mul_mem ((c.L ⊔ D.T).inv_mem hs'T) haiT) hsT)
      ((c.L ⊔ D.T).inv_mem hajT)
  exact ⟨hyLT, (sup_le c.L_le_stabTil c.T_le_stabTil) hyLT⟩

private theorem permutes_step (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    {a : G} (ha : a ∈ c.L)
    (hperm : (Subgroup.zpowers (c.phiL hV ⟨a, ha⟩ : MulAut (c.W hV)) :
          Set (MulAut (c.W hV))) * (c.Tstar hV : Set (MulAut (c.W hV))) =
        (c.Tstar hV : Set (MulAut (c.W hV))) *
          (Subgroup.zpowers (c.phiL hV ⟨a, ha⟩ : MulAut (c.W hV)) :
            Set (MulAut (c.W hV)))) :
    ∀ x ∈ Subgroup.zpowers a, ∀ s ∈ D.T,
      ∃ t ∈ D.T, ∃ y ∈ Subgroup.zpowers a, x * s = t * y := by
  classical
  have hQVT : c.QV ≤ D.T := c.QV_le_T hCLV
  intro x hx s hs
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hmem : (c.phiL hV ⟨a, ha⟩ : MulAut (c.W hV)) ^ i * c.phiT hV ⟨s, hs⟩ ∈
      (Subgroup.zpowers (c.phiL hV ⟨a, ha⟩ : MulAut (c.W hV)) :
          Set (MulAut (c.W hV))) * (c.Tstar hV : Set (MulAut (c.W hV))) :=
    Set.mem_mul.mpr ⟨_, Subgroup.zpow_mem_zpowers _ _, _,
      MonoidHom.mem_range.mpr ⟨⟨s, hs⟩, rfl⟩, rfl⟩
  rw [hperm] at hmem
  obtain ⟨tstar, htstar, beta, hbeta, htbeta⟩ := Set.mem_mul.mp hmem
  obtain ⟨⟨s', hs'⟩, hs'eq⟩ := MonoidHom.mem_range.mp htstar
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hbeta
  have hbetaeq : beta = (c.phiL hV ⟨a, ha⟩ : MulAut (c.W hV)) ^ j := hj.symm
  let y : G := s'⁻¹ * a ^ i * s * (a ^ j)⁻¹
  obtain ⟨hyLT, hy_stab⟩ := mem_sup_stabTil_inverter c hV ha hs hs' i j
  have hyact : actTil (⊥ : Subgroup G) c.V hV ⟨y, hy_stab⟩ = 1 :=
    actTil_inverter_eq_one c hV ha hs hs' i j tstar beta hs'eq htbeta hbetaeq hy_stab
  have hycent : y ∈ Subgroup.centralizer (c.V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := (actTil_eq_one_iff (⊥ : Subgroup G) c.V hV ⟨y, hy_stab⟩).1 hyact v hv
    rw [Subgroup.mem_bot] at h1
    have h2 : y * v * y⁻¹ = v := mul_inv_eq_one.mp h1
    calc v * y = (y * v * y⁻¹) * y := by rw [h2]
      _ = y * v := by group
  have hyT : y ∈ D.T := hQVT (Subgroup.mem_inf.mpr ⟨hyLT, hycent⟩)
  have hdecomp : a ^ i * s = s' * y * a ^ j := by
    simp only [y]
    group
  exact ⟨s' * y, D.T.mul_mem hs' hyT, a ^ j, Subgroup.zpow_mem_zpowers a j, hdecomp⟩

theorem permutes_of_phiL (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    {a : G} (ha : a ∈ c.L)
    (hperm : (Subgroup.zpowers (c.phiL hV ⟨a, ha⟩ : MulAut (c.W hV)) :
          Set (MulAut (c.W hV))) * (c.Tstar hV : Set (MulAut (c.W hV))) =
        (c.Tstar hV : Set (MulAut (c.W hV))) *
          (Subgroup.zpowers (c.phiL hV ⟨a, ha⟩ : MulAut (c.W hV)) :
            Set (MulAut (c.W hV)))) :
    Permutes (Subgroup.zpowers a) D.T := by
  classical
  have hQVT : c.QV ≤ D.T := c.QV_le_T hCLV
  have hstep := permutes_step c hV hCLV ha hperm
  rw [Permutes]
  ext g
  constructor
  · rintro ⟨x, hx, s, hs, rfl⟩
    obtain ⟨t, ht, y, hy, hty⟩ := hstep x hx s hs
    exact Set.mem_mul.mpr ⟨t, ht, y, hy, hty.symm⟩
  · rintro ⟨s, hs, x, hx, rfl⟩
    obtain ⟨t, ht, y, hy, hty⟩ := hstep x⁻¹ (Subgroup.inv_mem _ hx) s⁻¹ (D.T.inv_mem hs)
    refine Set.mem_mul.mpr ⟨y⁻¹, Subgroup.inv_mem _ hy, t⁻¹, D.T.inv_mem ht, ?_⟩
    have h1 : (t * y)⁻¹ = y⁻¹ * t⁻¹ := mul_inv_rev t y
    rw [← h1, ← hty]
    group

private def ModuleData (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) : Prop :=
  ∃ (r : ℕ) (a b w : MulAut (c.W hV)),
    r.Prime ∧ r ≠ 2 ∧ (∀ x ∈ c.Ztil hV, a x = x) ∧
    (c.Ztil hV).map (b : MulAut (c.W hV)).toMonoidHom = c.Ztil hV ∧
    (∃ x ∈ c.Ztil hV, b x ≠ x) ∧
    (c.Ztil hV).map (w : MulAut (c.W hV)).toMonoidHom ≠ c.Ztil hV ∧
    w * w = 1 ∧ w * a * w⁻¹ = a⁻¹ ∧ w * b * w⁻¹ = b⁻¹ ∧
    ((Subgroup.zpowers a : Set (MulAut (c.W hV))) *
        (c.Tstar hV : Set (MulAut (c.W hV))) =
      (c.Tstar hV : Set (MulAut (c.W hV))) * (Subgroup.zpowers a : Set (MulAut (c.W hV)))) ∧
    a ∈ c.H hV ∧ b ∈ c.H hV ∧ w ∈ c.H hV ∧
    orderOf a = r ∧ orderOf b = r ∧ a * b = b * a ∧
    IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)

private theorem exists_module_data (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (hA : KTab23a) (hK : KOrdNatural) (hS : KSchurL2) (hKP : KOmPlus)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hP : IsOmegaPlus (c.H hV) 4 (CFSG.Open.pRank 2 D.Z))
    (hNat : NatOmegaPlus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) :
    ModuleData c hV := by
  classical
  have hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) :=
    Or.inr (Or.inr (Or.inl ⟨hP, hNat⟩))
  obtain ⟨r, hr, hrdvd, a, haH, b, hbH, w, hwH, haord, hbord, hab, hafix, hbnorm,
    hbmove, hwsq, hwa, hwb, hwmove, haT⟩ :=
    hKP (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) (c.sylowStar hV) (c.Tstar hV)
      (c.omegaPlusFrame_of hV hA h4 h1930 hn2 hP hNat)
  have hfix : CFSG.Quasithin.fixV
      ((c.sylowStar hV : Subgroup ↥(c.H hV)).map (c.H hV).subtype) = c.Ztil hV :=
    c.fixV_sylowStar_eq_Ztil hV hA hnat h4 h1930
  have hn1 : 0 < CFSG.Open.pRank 2 D.Z := lt_of_lt_of_le (by norm_num) hn2
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hn1).not_two_dvd_nat hrdvd
  have hbmove' : ∃ x ∈ c.Ztil hV, b x ≠ x :=
    ⟨hbmove.choose, by rw [← hfix]; exact hbmove.choose_spec.1, hbmove.choose_spec.2⟩
  exact ⟨r, a, b, w, hr, hr2, fun x hx => hafix x (hfix.symm ▸ hx), hfix ▸ hbnorm, hbmove',
    hfix ▸ hwmove, hwsq, hwa, hwb, haT, haH, hbH, hwH, haord, hbord, hab, hnat⟩

private theorem exists_omegaPlusTorus_of_data (c : Ctx23L D Ch) {r : ℕ} {z₁ z₂ t : ↥c.L}
    (hr : r.Prime) (hr2 : r ≠ 2) (hz₁ord : orderOf z₁ = r) (hz₂ord : orderOf z₂ = r)
    (hz₁z₂ : z₁ * z₂ = z₂ * z₁) (hz₁cent : (z₁ : G) ∈ Subgroup.centralizer (D.Z : Set G))
    (hz₂M : (z₂ : G) ∈ D.M) (hz₂NotCent : (z₂ : G) ∉ Subgroup.centralizer (D.Z : Set G))
    (htM : (t : G) ∉ D.M) {k : ℕ} (hto : orderOf t = 2 ^ k)
    (ht_inv : ∀ z ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂, t * z * t⁻¹ = z⁻¹)
    (hpermutes : Permutes (Subgroup.zpowers (z₁ : G)) D.T) :
    ∃ r a b t, OmegaPlusTorus c r a b t := by
  refine ⟨r, z₁, z₂, (t : G), ?_⟩
  have hz₁ordG : orderOf (z₁ : G) = r := by rw [Subgroup.orderOf_coe, hz₁ord]
  have hz₂ordG : orderOf (z₂ : G) = r := by rw [Subgroup.orderOf_coe, hz₂ord]
  have hcomm : (z₁ : G) * z₂ = (z₂ : G) * z₁ :=
    congrArg (fun x : ↥c.L => (x : G)) hz₁z₂
  have htord : ∃ k : ℕ, orderOf (t : G) = 2 ^ k :=
    ⟨k, by rw [Subgroup.orderOf_coe]; exact hto⟩
  have hle₁ : Subgroup.zpowers z₁ ≤ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ := le_sup_left
  have hle₂ : Subgroup.zpowers z₂ ≤ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ := le_sup_right
  have hinva : (t : G) * z₁ * (t : G)⁻¹ = z₁⁻¹ := by
    simpa using congrArg (fun x : ↥c.L => (x : G)) (ht_inv z₁ (hle₁ (Subgroup.mem_zpowers z₁)))
  have hinvb : (t : G) * z₂ * (t : G)⁻¹ = z₂⁻¹ := by
    simpa using congrArg (fun x : ↥c.L => (x : G)) (ht_inv z₂ (hle₂ (Subgroup.mem_zpowers z₂)))
  exact ⟨hr, hr2, z₁.2, z₂.2, t.2, hz₁ordG, hz₂ordG, hcomm, hz₁cent, hz₂M, hz₂NotCent, htM,
    htord, hinva, hinvb, hpermutes⟩

private theorem permutes_lift (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    {a : MulAut (c.W hV)} (haH : a ∈ c.H hV) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (haord : orderOf a = r)
    (haT : (Subgroup.zpowers a : Set (MulAut (c.W hV))) *
        (c.Tstar hV : Set (MulAut (c.W hV))) =
      (c.Tstar hV : Set (MulAut (c.W hV))) * (Subgroup.zpowers a : Set (MulAut (c.W hV))))
    {z₁ : ↥c.L} (hz₁ne : z₁ ≠ 1) (hz₁ord : orderOf z₁ = r)
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    (hφ₁ : c.phiL hV z₁ ∈ Subgroup.zpowers (⟨a, haH⟩ : ↥(c.H hV))) :
    Permutes (Subgroup.zpowers (z₁ : G)) D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hφ₁ne : c.phiL hV z₁ ≠ 1 := by
    intro h
    have hz₁Q : z₁ ∈ CFSG.pCore 2 ↥c.L := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr h
    have h2 : 2 ∣ orderOf z₁ := by
      simpa only [Subgroup.orderOf_mk] using
        (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).dvd_orderOf
          (g := (⟨z₁, hz₁Q⟩ : ↥(CFSG.pCore 2 ↥c.L)))
          (fun hh => hz₁ne (congrArg Subtype.val hh))
    rw [hz₁ord] at h2
    exact (hr.odd_of_ne_two hr2).not_two_dvd_nat h2
  have hperm : (Subgroup.zpowers (c.phiL hV z₁ : MulAut (c.W hV)) :
        Set (MulAut (c.W hV))) * (c.Tstar hV : Set (MulAut (c.W hV))) =
      (c.Tstar hV : Set (MulAut (c.W hV))) *
        (Subgroup.zpowers (c.phiL hV z₁ : MulAut (c.W hV)) :
          Set (MulAut (c.W hV))) := by
    have hφ₁amb : (c.phiL hV z₁ : MulAut (c.W hV)) ∈ Subgroup.zpowers a := by
      have hh := Subgroup.mem_map_of_mem (f := (c.H hV).subtype) hφ₁
      simpa only [MonoidHom.map_zpowers, Subgroup.coe_subtype] using hh
    have hane : (c.phiL hV z₁ : MulAut (c.W hV)) ≠ 1 := fun h => hφ₁ne (Subtype.ext h)
    have har : a ^ r = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [haord])
    have hzpow₁amb : Subgroup.zpowers (c.phiL hV z₁ : MulAut (c.W hV)) =
        Subgroup.zpowers a :=
      TauCeti.zpowers_eq_zpowers_of_mem_zpowers hr har hane hφ₁amb
    show (Subgroup.zpowers (c.phiL hV z₁ : MulAut (c.W hV)) :
        Set (MulAut (c.W hV))) * (c.Tstar hV : Set (MulAut (c.W hV))) = _
    rw [hzpow₁amb]
    exact haT
  exact c.permutes_of_phiL hV hCLV z₁.2 hperm

private theorem w₁_commutator_mem (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hkerQ : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) {z₁ z₂ w₁ : ↥c.L} {w : MulAut (c.W hV)}
    (hwH : w ∈ c.H hV) (hw₁φ : c.phiL hV w₁ = ⟨w, hwH⟩)
    (hconjE : ∀ e ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂,
      (⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV e * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹ = (c.phiL hV e)⁻¹) :
    ∀ e ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂,
      w₁ * e * w₁⁻¹ * e ∈ CFSG.pCore 2 ↥c.L := by
  intro e he
  have h1 : c.phiL hV (w₁ * e * w₁⁻¹ * e) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hw₁φ, hconjE e he]
    group
  rw [← hkerQ]
  exact MonoidHom.mem_ker.mpr h1

private theorem Y_odd_inf (c : Ctx23L D Ch) {z₁ z₂ w₁ : ↥c.L}
    (hQ2 : IsPGroup 2 (CFSG.pCore 2 ↥c.L))
    (hEodd : ∀ x ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂, Odd (orderOf x)) :
    (∀ y ∈ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map (MulAut.conj w₁).toMonoidHom,
        Odd (orderOf y)) ∧
      CFSG.pCore 2 ↥c.L ⊓
        (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map (MulAut.conj w₁).toMonoidHom = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYodd : ∀ y ∈ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map
      (MulAut.conj w₁).toMonoidHom, Odd (orderOf y) := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
    rw [MulEquiv.coe_toMonoidHom, (MulAut.conj w₁).orderOf_eq e]
    exact hEodd e he
  have hQY : CFSG.pCore 2 ↥c.L ⊓ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map
      (MulAut.conj w₁).toMonoidHom = ⊥ := by
    rw [inf_comm]
    exact CFSG.OddStandard.SmallF3.Omega.sec4_isPGroup_inf_eq_bot_of_odd_orderOf hYodd hQ2
  exact ⟨hYodd, hQY⟩

private theorem Y_sup (c : Ctx23L D Ch) {z₁ z₂ w₁ : ↥c.L}
    (hwe : ∀ e ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂,
      w₁ * e * w₁⁻¹ * e ∈ CFSG.pCore 2 ↥c.L) :
    (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map (MulAut.conj w₁).toMonoidHom ≤
        CFSG.pCore 2 ↥c.L ⊔ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) ∧
      CFSG.pCore 2 ↥c.L ⊔ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map
          (MulAut.conj w₁).toMonoidHom =
        CFSG.pCore 2 ↥c.L ⊔ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) := by
  let E : Subgroup ↥c.L := Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂
  let Y : Subgroup ↥c.L := E.map (MulAut.conj w₁).toMonoidHom
  have hYle : Y ≤ CFSG.pCore 2 ↥c.L ⊔ E := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
    rw [MulEquiv.coe_toMonoidHom]
    have hq : w₁ * e * w₁⁻¹ * e ∈ CFSG.pCore 2 ↥c.L := hwe e he
    have heq : MulAut.conj w₁ e = (w₁ * e * w₁⁻¹ * e) * e⁻¹ := by
      rw [MulAut.conj_apply]
      group
    rw [heq]
    exact Subgroup.mul_mem _ ((le_sup_left : CFSG.pCore 2 ↥c.L ≤ CFSG.pCore 2 ↥c.L ⊔ E) hq)
      ((le_sup_right : E ≤ CFSG.pCore 2 ↥c.L ⊔ E) (E.inv_mem he))
  have hE_le : E ≤ CFSG.pCore 2 ↥c.L ⊔ Y := by
    intro e he
    have hq : w₁ * e * w₁⁻¹ * e ∈ CFSG.pCore 2 ↥c.L := hwe e he
    have hy : w₁ * e * w₁⁻¹ ∈ Y := by
      have h := Subgroup.mem_map_of_mem (f := (MulAut.conj w₁).toMonoidHom) he
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      exact h
    have heq : e = (w₁ * e * w₁⁻¹)⁻¹ * (w₁ * e * w₁⁻¹ * e) := by group
    rw [heq]
    exact Subgroup.mul_mem _ ((le_sup_right : Y ≤ CFSG.pCore 2 ↥c.L ⊔ Y) (Subgroup.inv_mem _ hy))
      ((le_sup_left : CFSG.pCore 2 ↥c.L ≤ CFSG.pCore 2 ↥c.L ⊔ Y) hq)
  exact ⟨hYle, le_antisymm (sup_le le_sup_left hYle) (sup_le le_sup_left hE_le)⟩

private theorem Y_facts (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) {z₁ z₂ w₁ : ↥c.L} {w : MulAut (c.W hV)}
    (hwH : w ∈ c.H hV) (hw₁φ : c.phiL hV w₁ = ⟨w, hwH⟩)
    (hconjE : ∀ e ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂,
      (⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV e * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹ = (c.phiL hV e)⁻¹)
    (hQ2 : IsPGroup 2 (CFSG.pCore 2 ↥c.L))
    (hEodd : ∀ x ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂, Odd (orderOf x)) :
    (∀ y ∈ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map (MulAut.conj w₁).toMonoidHom,
        Odd (orderOf y)) ∧
      CFSG.pCore 2 ↥c.L ⊓ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map
          (MulAut.conj w₁).toMonoidHom = ⊥ ∧
      (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map (MulAut.conj w₁).toMonoidHom ≤
        CFSG.pCore 2 ↥c.L ⊔ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) ∧
      CFSG.pCore 2 ↥c.L ⊔ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map
          (MulAut.conj w₁).toMonoidHom =
        CFSG.pCore 2 ↥c.L ⊔ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) := by
  have hwe := w₁_commutator_mem c hV hker hwH hw₁φ hconjE
  obtain ⟨hYodd, hQY⟩ := Y_odd_inf c hQ2 hEodd
  obtain ⟨hYle, hQY_eq⟩ := Y_sup c hwe
  exact ⟨hYodd, hQY, hYle, hQY_eq⟩

private theorem exists_conj_complement (c : Ctx23L D Ch) {z₁ z₂ w₁ : ↥c.L}
    (hEQ : (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) ⊓ CFSG.pCore 2 ↥c.L = ⊥)
    (hQY : CFSG.pCore 2 ↥c.L ⊓ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map
        (MulAut.conj w₁).toMonoidHom = ⊥)
    (hYle : (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map (MulAut.conj w₁).toMonoidHom ≤
        CFSG.pCore 2 ↥c.L ⊔ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂))
    (hQY_eq : CFSG.pCore 2 ↥c.L ⊔ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map
          (MulAut.conj w₁).toMonoidHom =
        CFSG.pCore 2 ↥c.L ⊔ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂))
    (hodd : ¬ 2 ∣ (CFSG.pCore 2 ↥c.L).relIndex
        (CFSG.pCore 2 ↥c.L ⊔ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂))) :
    ∃ r₀ ∈ CFSG.pCore 2 ↥c.L,
      (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map (MulAut.conj w₁).toMonoidHom =
        CFSG.QuasithinUnique.conjR (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) r₀ := by
  let E : Subgroup ↥c.L := Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂
  let Y : Subgroup ↥c.L := E.map (MulAut.conj w₁).toMonoidHom
  let F : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L ⊔ E
  have hFE : ∀ f ∈ F, ∃ q ∈ CFSG.pCore 2 ↥c.L, ∃ b ∈ E, f = q * b := by
    intro f hf
    have hf' : f ∈ (CFSG.pCore 2 ↥c.L : Set ↥c.L) * (E : Set ↥c.L) := by
      rw [← Subgroup.normal_mul]
      exact hf
    obtain ⟨q, hq, b, hb, hqb⟩ := Set.mem_mul.mp hf'
    exact ⟨q, hq, b, hb, hqb.symm⟩
  have hFY : ∀ f ∈ F, ∃ q ∈ CFSG.pCore 2 ↥c.L, ∃ b ∈ Y, f = q * b := by
    intro f hf
    have hf' : f ∈ (CFSG.pCore 2 ↥c.L : Set ↥c.L) * (Y : Set ↥c.L) := by
      rw [← Subgroup.normal_mul, hQY_eq]
      exact hf
    obtain ⟨q, hq, b, hb, hqb⟩ := Set.mem_mul.mp hf'
    exact ⟨q, hq, b, hb, hqb.symm⟩
  exact CFSG.QuasithinUnique.Lin2.exists_conj_of_complements
    (F := F) (R := CFSG.pCore 2 ↥c.L) (B := E) (B' := Y)
    (le_sup_left : CFSG.pCore 2 ↥c.L ≤ F) (by
      rw [Subgroup.normalizer_eq_top_iff.mpr
        (inferInstance : (CFSG.pCore 2 ↥c.L).Normal)]
      exact le_top) (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) hodd
    (le_sup_right : E ≤ F) hYle (by rw [inf_comm]; exact hEQ) hQY hFE hFY

private theorem exists_tL (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hkerQ : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) {r₀ w₁ : ↥c.L}
    (hr₀ : r₀ ∈ CFSG.pCore 2 ↥c.L) {w : MulAut (c.W hV)} (hwH : w ∈ c.H hV)
    (hw₁φ : c.phiL hV w₁ = ⟨w, hwH⟩) :
    ∃ tL : ↥c.L, tL = r₀ * w₁ ∧ c.phiL hV tL = ⟨w, hwH⟩ := by
  refine ⟨r₀ * w₁, rfl, ?_⟩
  have hr₀ker : c.phiL hV r₀ = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hkerQ]
    exact hr₀
  rw [map_mul, hr₀ker, one_mul, hw₁φ]

private theorem tL_inv (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hkerQ : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) {z₁ z₂ : ↥c.L}
    (hEQ : (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) ⊓ CFSG.pCore 2 ↥c.L = ⊥)
    {r₀ w₁ tL : ↥c.L} (htL : tL = r₀ * w₁)
    (hYeq : (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map (MulAut.conj w₁).toMonoidHom =
      CFSG.QuasithinUnique.conjR (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) r₀)
    {w : MulAut (c.W hV)} (hwH : w ∈ c.H hV)
    (hconjE : ∀ e ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂,
      (⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV e * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹ = (c.phiL hV e)⁻¹)
    (htφ : c.phiL hV tL = ⟨w, hwH⟩) :
    ∀ z ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂, tL * z * tL⁻¹ = z⁻¹ := by
  let E : Subgroup ↥c.L := Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂
  intro z hz
  have hzE : tL * z * tL⁻¹ ∈ E := by
    have hy : w₁ * z * w₁⁻¹ ∈ E.map (MulAut.conj w₁).toMonoidHom := by
      have h := Subgroup.mem_map_of_mem (f := (MulAut.conj w₁).toMonoidHom) hz
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      exact h
    rw [hYeq, CFSG.QuasithinUnique.Lin2.mem_conjR] at hy
    have heq : tL * z * tL⁻¹ = r₀ * (w₁ * z * w₁⁻¹) * r₀⁻¹ := by
      rw [htL]
      group
    rw [heq]
    exact hy
  have hq : tL * z * tL⁻¹ * z ∈ CFSG.pCore 2 ↥c.L := by
    have h1 : c.phiL hV (tL * z * tL⁻¹ * z) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, htφ, hconjE z hz]
      group
    rw [← hkerQ]
    exact MonoidHom.mem_ker.mpr h1
  have h1 : tL * z * tL⁻¹ * z = 1 := by
    have hinf : tL * z * tL⁻¹ * z ∈ E ⊓ CFSG.pCore 2 ↥c.L :=
      Subgroup.mem_inf.mpr ⟨E.mul_mem hzE hz, hq⟩
    rwa [hEQ, Subgroup.mem_bot] at hinf
  calc tL * z * tL⁻¹ = (tL * z * tL⁻¹ * z) * z⁻¹ := by group
    _ = z⁻¹ := by rw [h1, one_mul]

private theorem orderOf_pow_two (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {tL : ↥c.L} {w : MulAut (c.W hV)} (hwH : w ∈ c.H hV) (hwsq : w * w = 1)
    (hkerQ : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    (htφ : c.phiL hV tL = ⟨w, hwH⟩) :
    ∃ k : ℕ, orderOf tL = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2Q : tL * tL ∈ CFSG.pCore 2 ↥c.L := by
    have hww : (⟨w, hwH⟩ : ↥(c.H hV)) * ⟨w, hwH⟩ = 1 := Subtype.ext hwsq
    have h1 : c.phiL hV (tL * tL) = 1 := by
      rw [map_mul, htφ, hww]
    rw [← hkerQ]
    exact MonoidHom.mem_ker.mpr h1
  obtain ⟨k, hk⟩ := ((CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).to_le
    (Subgroup.zpowers_le.mpr ht2Q)).exists_card_eq
  have hk' : orderOf (tL * tL) = 2 ^ k := by
    rw [← hk, Nat.card_zpowers]
  have hpow : tL ^ (2 ^ (k + 1)) = 1 := by
    have h2 : (tL * tL) ^ (2 ^ k) = tL ^ (2 ^ (k + 1)) := by
      rw [← pow_two, ← pow_mul, ← pow_succ' 2 k]
    rw [← h2, ← hk']
    exact pow_orderOf_eq_one (tL * tL)
  have hdvd : orderOf tL ∣ 2 ^ (k + 1) := orderOf_dvd_iff_pow_eq_one.mpr hpow
  obtain ⟨j, -, hj⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two (m := k + 1) (i := orderOf tL)).mp hdvd
  exact ⟨j, hj⟩

private theorem tL_not_mem_M (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) {tL : ↥c.L} {w : MulAut (c.W hV)} (hwH : w ∈ c.H hV)
    (hwmove : (c.Ztil hV).map w.toMonoidHom ≠ c.Ztil hV)
    (htφ : c.phiL hV tL = ⟨w, hwH⟩) : (tL : G) ∉ D.M := by
  intro ht
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  have hstab := (c.phiL_mem_stabilizer_Ztil_iff hV h4 h1930 tL).2 ht
  rw [htφ] at hstab
  have hstab' : (⟨w, hwH⟩ : ↥(c.H hV)) • (c.Ztil hV : Set (c.W hV)) =
      ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)) :=
    MulAction.mem_stabilizer_iff.mp hstab
  have hcoe : (⟨w, hwH⟩ : ↥(c.H hV)) • (c.Ztil hV : Set (c.W hV)) =
      (((c.Ztil hV).map w.toMonoidHom) : Set (c.W hV)) := by
    rw [Subgroup.coe_map, ← Set.image_smul]
    rfl
  rw [hcoe] at hstab'
  exact hwmove (Subgroup.ext (Set.ext_iff.mp hstab'))

private theorem exists_lift_root (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (e : Bar2 c.L ≃* ↥(c.H hV))
    (he_mk : ∀ x : ↥c.L, e (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) x) = c.phiL hV x)
    {a : MulAut (c.W hV)} (haH : a ∈ c.H hV) {r : ℕ} (haord : orderOf a = r)
    (hr : r.Prime) (hr2 : r ≠ 2) (hafix : ∀ x ∈ c.Ztil hV, a x = x) :
    ∃ z₁ : ↥c.L, z₁ ≠ 1 ∧ orderOf z₁ = r ∧
      c.phiL hV z₁ ∈ Subgroup.zpowers (⟨a, haH⟩ : ↥(c.H hV)) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) z₁ ∈ Subgroup.zpowers (e.symm ⟨a, haH⟩) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have haH1 : (⟨a, haH⟩ : ↥(c.H hV)) ≠ 1 := by
    intro h
    have h1 : orderOf (⟨a, haH⟩ : ↥(c.H hV)) = 1 := by rw [h, orderOf_one]
    rw [← Subgroup.orderOf_coe, haord] at h1
    exact hr.ne_one h1
  have haHr : (⟨a, haH⟩ : ↥(c.H hV)) ^ r = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← Subgroup.orderOf_coe, haord]
  have hxa1 : e.symm ⟨a, haH⟩ ≠ 1 := by
    intro h
    have h1 : (⟨a, haH⟩ : ↥(c.H hV)) = 1 := by
      rw [← MulEquiv.apply_symm_apply e ⟨a, haH⟩, h, map_one]
    exact haH1 h1
  have hxar : (e.symm ⟨a, haH⟩) ^ r = 1 := by
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    exact haHr
  obtain ⟨z₁, -, hz₁r, hz₁ne, hz₁mem⟩ :=
    exists_pow_eq_one_commute_of_commute_bar (M := c.L) (b := (1 : ↥c.L))
      (by simpa using odd_one) hr hr2 hxa1 hxar (by simp)
  have hz₁ord : orderOf z₁ = r := orderOf_eq_prime hz₁r hz₁ne
  have hφ₁ : c.phiL hV z₁ ∈ Subgroup.zpowers (⟨a, haH⟩ : ↥(c.H hV)) := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz₁mem
    have h1 : c.phiL hV z₁ = (⟨a, haH⟩ : ↥(c.H hV)) ^ m := by
      rw [← he_mk z₁, ← hm, map_zpow]
      exact congrArg (· ^ m) (MulEquiv.apply_symm_apply e ⟨a, haH⟩)
    rw [h1]
    exact Subgroup.zpow_mem_zpowers (⟨a, haH⟩ : ↥(c.H hV)) m
  exact ⟨z₁, hz₁ne, hz₁ord, hφ₁, hz₁mem⟩

private theorem root_centralizes (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {a : MulAut (c.W hV)} (haH : a ∈ c.H hV) (hafix : ∀ x ∈ c.Ztil hV, a x = x)
    {z₁ : ↥c.L} (hφ₁ : c.phiL hV z₁ ∈ Subgroup.zpowers (⟨a, haH⟩ : ↥(c.H hV))) :
    (z₁ : G) ∈ Subgroup.centralizer (D.Z : Set G) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  have hafixmem : (⟨a, haH⟩ : ↥(c.H hV)) ∈ fixingSubgroupOf ↥(c.H hV) (c.W hV)
      ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)) := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    simpa [MulAction.compHom_smul_def, MulAut.smul_def] using hafix x hx
  exact (c.phiL_mem_fixingSubgroup_Ztil_iff hV z₁).1
    ((Subgroup.zpowers_le.mpr hafixmem) hφ₁)

private theorem exists_lift_diag (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (e : Bar2 c.L ≃* ↥(c.H hV))
    (he_mk : ∀ x : ↥c.L, e (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) x) = c.phiL hV x)
    {a b : MulAut (c.W hV)} (haH : a ∈ c.H hV) (hbH : b ∈ c.H hV) (hab : a * b = b * a)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hbord : orderOf b = r) {z₁ : ↥c.L}
    (hz₁ord : orderOf z₁ = r)
    (hz₁mem : QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) z₁ ∈ Subgroup.zpowers (e.symm ⟨a, haH⟩)) :
    ∃ z₂ : ↥c.L, z₂ * z₁ = z₁ * z₂ ∧ orderOf z₂ = r ∧ z₂ ≠ 1 ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) z₂ ∈ Subgroup.zpowers (e.symm ⟨b, hbH⟩) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hbH1 : (⟨b, hbH⟩ : ↥(c.H hV)) ≠ 1 := by
    intro h
    have h1 : orderOf (⟨b, hbH⟩ : ↥(c.H hV)) = 1 := by rw [h, orderOf_one]
    rw [← Subgroup.orderOf_coe, hbord] at h1
    exact hr.ne_one h1
  have hbHr : (⟨b, hbH⟩ : ↥(c.H hV)) ^ r = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← Subgroup.orderOf_coe, hbord]
  have hxb1 : e.symm ⟨b, hbH⟩ ≠ 1 := by
    intro h
    have h1 : (⟨b, hbH⟩ : ↥(c.H hV)) = 1 := by
      rw [← MulEquiv.apply_symm_apply e ⟨b, hbH⟩, h, map_one]
    exact hbH1 h1
  have hxbr : (e.symm ⟨b, hbH⟩) ^ r = 1 := by
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    exact hbHr
  have hcommH : (⟨a, haH⟩ : ↥(c.H hV)) * ⟨b, hbH⟩ = ⟨b, hbH⟩ * ⟨a, haH⟩ :=
    Subtype.ext hab
  have hcomm_ab :
      e.symm ⟨a, haH⟩ * e.symm ⟨b, hbH⟩ = e.symm ⟨b, hbH⟩ * e.symm ⟨a, haH⟩ := by
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hcommH
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz₁mem
  have hcommq : QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) z₁ * e.symm ⟨b, hbH⟩ =
      e.symm ⟨b, hbH⟩ * QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) z₁ := by
    rw [← hn]
    exact (show Commute (e.symm ⟨a, haH⟩) (e.symm ⟨b, hbH⟩) from hcomm_ab).zpow_left n |>.eq
  obtain ⟨z₂, hz₂comm, hz₂r, hz₂ne, hz₂mem⟩ :=
    exists_pow_eq_one_commute_of_commute_bar (M := c.L) (b := z₁)
      (by rw [hz₁ord]; exact hr.odd_of_ne_two hr2) hr hr2 hxb1 hxbr hcommq
  exact ⟨z₂, hz₂comm, orderOf_eq_prime hz₂r hz₂ne, hz₂ne, hz₂mem⟩

private theorem diag_phiL_mem (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (e : Bar2 c.L ≃* ↥(c.H hV))
    (he_mk : ∀ x : ↥c.L, e (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) x) = c.phiL hV x)
    {b : MulAut (c.W hV)} (hbH : b ∈ c.H hV) {z₂ : ↥c.L}
    (hz₂mem : QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) z₂ ∈
      Subgroup.zpowers (e.symm ⟨b, hbH⟩)) :
    c.phiL hV z₂ ∈ Subgroup.zpowers (⟨b, hbH⟩ : ↥(c.H hV)) := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz₂mem
  have h1 : c.phiL hV z₂ = (⟨b, hbH⟩ : ↥(c.H hV)) ^ m := by
    rw [← he_mk z₂, ← hm, map_zpow]
    exact congrArg (· ^ m) (MulEquiv.apply_symm_apply e ⟨b, hbH⟩)
  rw [h1]
  exact Subgroup.zpow_mem_zpowers (⟨b, hbH⟩ : ↥(c.H hV)) m

private theorem diag_mem_M (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) {b : MulAut (c.W hV)} (hbH : b ∈ c.H hV)
    (hbnorm : (c.Ztil hV).map b.toMonoidHom = c.Ztil hV) {z₂ : ↥c.L}
    (hφ₂ : c.phiL hV z₂ ∈ Subgroup.zpowers (⟨b, hbH⟩ : ↥(c.H hV))) :
    (z₂ : G) ∈ D.M := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  have hbStab : (⟨b, hbH⟩ : ↥(c.H hV)) ∈ MulAction.stabilizer ↥(c.H hV)
      ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)) := by
    rw [MulAction.mem_stabilizer_iff]
    have hcoe : (⟨b, hbH⟩ : ↥(c.H hV)) • (c.Ztil hV : Set (c.W hV)) =
        (((c.Ztil hV).map b.toMonoidHom) : Set (c.W hV)) := by
      rw [Subgroup.coe_map, ← Set.image_smul]
      rfl
    rw [hcoe, hbnorm]
  exact (c.phiL_mem_stabilizer_Ztil_iff hV h4 h1930 z₂).1
    ((Subgroup.zpowers_le.mpr hbStab) hφ₂)

private theorem diag_phiL_ne_one (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {z₂ : ↥c.L} (hz₂ord : orderOf z₂ = r) (hz₂ne : z₂ ≠ 1) :
    c.phiL hV z₂ ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz₂Q : z₂ ∉ CFSG.pCore 2 ↥c.L := by
    intro hz
    have h2 : 2 ∣ orderOf z₂ := by
      simpa only [Subgroup.orderOf_mk] using
        (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).dvd_orderOf
          (g := (⟨z₂, hz⟩ : ↥(CFSG.pCore 2 ↥c.L)))
          (fun h => hz₂ne (congrArg Subtype.val h))
    rw [hz₂ord] at h2
    exact (hr.odd_of_ne_two hr2).not_two_dvd_nat h2
  intro h
  exact hz₂Q (hker ▸ MonoidHom.mem_ker.mpr h)

private theorem diag_not_centralizes (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {b : MulAut (c.W hV)} (hbH : b ∈ c.H hV) {r : ℕ} (hr : r.Prime)
    (hbord : orderOf b = r) (hbmove : ∃ x ∈ c.Ztil hV, b x ≠ x) {z₂ : ↥c.L}
    (hφ₂ : c.phiL hV z₂ ∈ Subgroup.zpowers (⟨b, hbH⟩ : ↥(c.H hV)))
    (hφ₂ne : c.phiL hV z₂ ≠ 1) :
    (z₂ : G) ∉ Subgroup.centralizer (D.Z : Set G) := by
  intro hcent
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  have hfix₂ : c.phiL hV z₂ ∈ fixingSubgroupOf ↥(c.H hV) (c.W hV)
      ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)) :=
    (c.phiL_mem_fixingSubgroup_Ztil_iff hV z₂).2 hcent
  have hbHr : (⟨b, hbH⟩ : ↥(c.H hV)) ^ r = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← Subgroup.orderOf_coe, hbord]
  have hzp : Subgroup.zpowers (c.phiL hV z₂) =
      Subgroup.zpowers (⟨b, hbH⟩ : ↥(c.H hV)) :=
    TauCeti.zpowers_eq_zpowers_of_mem_zpowers hr hbHr hφ₂ne hφ₂
  have hbFix : (⟨b, hbH⟩ : ↥(c.H hV)) ∈ fixingSubgroupOf ↥(c.H hV) (c.W hV)
      ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)) := by
    have hle := (Subgroup.zpowers_le.mpr hfix₂ : Subgroup.zpowers (c.phiL hV z₂) ≤ _)
    rw [hzp] at hle
    exact Subgroup.zpowers_le.mp hle
  have hbpoint : ∀ x ∈ c.Ztil hV, b x = x := by
    intro x hx
    have h := (mem_fixingSubgroup_iff (M := ↥(c.H hV))).1 hbFix x hx
    simpa [MulAction.compHom_smul_def, MulAut.smul_def] using h
  obtain ⟨x, hx, hbx⟩ := hbmove
  exact hbx (hbpoint x hx)

private theorem exists_lift_torus (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (e : Bar2 c.L ≃* ↥(c.H hV))
    (he_mk : ∀ x : ↥c.L, e (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) x) = c.phiL hV x)
    {a b : MulAut (c.W hV)} (haH : a ∈ c.H hV) (hbH : b ∈ c.H hV)
    (hab : a * b = b * a) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (haord : orderOf a = r) (hbord : orderOf b = r) (hafix : ∀ x ∈ c.Ztil hV, a x = x)
    (hbnorm : (c.Ztil hV).map b.toMonoidHom = c.Ztil hV)
    (hbmove : ∃ x ∈ c.Ztil hV, b x ≠ x)
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    ∃ z₁ z₂ : ↥c.L, z₁ ≠ 1 ∧ orderOf z₁ = r ∧
      c.phiL hV z₁ ∈ Subgroup.zpowers (⟨a, haH⟩ : ↥(c.H hV)) ∧
      (z₁ : G) ∈ Subgroup.centralizer (D.Z : Set G) ∧
      z₂ * z₁ = z₁ * z₂ ∧ orderOf z₂ = r ∧
      c.phiL hV z₂ ∈ Subgroup.zpowers (⟨b, hbH⟩ : ↥(c.H hV)) ∧
      (z₂ : G) ∈ D.M ∧ (z₂ : G) ∉ Subgroup.centralizer (D.Z : Set G) := by
  obtain ⟨z₁, hz₁ne, hz₁ord, hφ₁, hz₁mem⟩ :=
    exists_lift_root c hV e he_mk haH haord hr hr2 hafix
  have haz := root_centralizes c hV haH hafix hφ₁
  obtain ⟨z₂, hz₂comm, hz₂ord, hz₂ne, hz₂mem⟩ :=
    exists_lift_diag c hV e he_mk haH hbH hab hr hr2 hbord hz₁ord hz₁mem
  have hφ₂ := diag_phiL_mem c hV e he_mk hbH hz₂mem
  have hbM := diag_mem_M c hV h4 h1930 hbH hbnorm hφ₂
  have hφ₂ne := diag_phiL_ne_one c hV hker hr hr2 hz₂ord hz₂ne
  have hbNotCent := diag_not_centralizes c hV hbH hr hbord hbmove hφ₂ hφ₂ne
  exact ⟨z₁, z₂, hz₁ne, hz₁ord, hφ₁, haz, hz₂comm, hz₂ord, hφ₂, hbM, hbNotCent⟩

private theorem torus_pow (c : Ctx23L D Ch) {z₁ z₂ : ↥c.L} {r : ℕ} (hr : r.Prime)
    (hz₁ord : orderOf z₁ = r) (hz₂ord : orderOf z₂ = r) (hz₁z₂ : z₁ * z₂ = z₂ * z₁) :
    (∀ u ∈ Subgroup.zpowers z₁, ∀ v ∈ Subgroup.zpowers z₂, u * v = v * u) ∧
      (∀ u ∈ Subgroup.zpowers z₁, u ^ r = 1) ∧
      (∀ v ∈ Subgroup.zpowers z₂, v ^ r = 1) := by
  have hcomm_z : ∀ u ∈ Subgroup.zpowers z₁, ∀ v ∈ Subgroup.zpowers z₂, u * v = v * u := by
    intro u hu v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute z₁ z₂ from hz₁z₂).zpow_left m).zpow_right n |>.eq
  have hpow₁ : ∀ u ∈ Subgroup.zpowers z₁, u ^ r = 1 := by
    intro u hu
    have hdvd : orderOf u ∣ r := by
      rw [← hz₁ord]
      exact orderOf_dvd_of_mem_zpowers hu
    rcases (Nat.dvd_prime hr).mp hdvd with h1 | hr'
    · rw [orderOf_eq_one_iff.mp h1, one_pow]
    · rw [← hr']
      exact pow_orderOf_eq_one u
  have hpow₂ : ∀ v ∈ Subgroup.zpowers z₂, v ^ r = 1 := by
    intro v hv
    have hdvd : orderOf v ∣ r := by
      rw [← hz₂ord]
      exact orderOf_dvd_of_mem_zpowers hv
    rcases (Nat.dvd_prime hr).mp hdvd with h1 | hr'
    · rw [orderOf_eq_one_iff.mp h1, one_pow]
    · rw [← hr']
      exact pow_orderOf_eq_one v
  exact ⟨hcomm_z, hpow₁, hpow₂⟩

private theorem torus_odd (c : Ctx23L D Ch) {z₁ z₂ : ↥c.L} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hcomm_z : ∀ u ∈ Subgroup.zpowers z₁, ∀ v ∈ Subgroup.zpowers z₂, u * v = v * u)
    (hpow₁ : ∀ u ∈ Subgroup.zpowers z₁, u ^ r = 1)
    (hpow₂ : ∀ v ∈ Subgroup.zpowers z₂, v ^ r = 1) :
    ∀ x ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂, Odd (orderOf x) := by
  intro x hx
  obtain ⟨u, hu, v, hv, huv⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm_z hx
  have hxr : x ^ r = 1 := by
    rw [← huv, (show Commute u v from hcomm_z u hu v hv).mul_pow, hpow₁ u hu,
      hpow₂ v hv, mul_one]
  have hdvd : orderOf x ∣ r := orderOf_dvd_iff_pow_eq_one.mpr hxr
  rcases (Nat.dvd_prime hr).mp hdvd with h1 | hr'
  · rw [h1]
    exact odd_one
  · rw [hr']
    exact hr.odd_of_ne_two hr2

private theorem torus_inf_bot (c : Ctx23L D Ch) {z₁ z₂ : ↥c.L}
    (hQ2 : IsPGroup 2 (CFSG.pCore 2 ↥c.L))
    (hEodd : ∀ x ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂, Odd (orderOf x)) :
    (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) ⊓ CFSG.pCore 2 ↥c.L = ⊥ :=
  CFSG.OddStandard.SmallF3.Omega.sec4_isPGroup_inf_eq_bot_of_odd_orderOf hEodd hQ2

private theorem torus_index (c : Ctx23L D Ch) {z₁ z₂ : ↥c.L}
    (hEQ : (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) ⊓ CFSG.pCore 2 ↥c.L = ⊥)
    (hEodd : ∀ x ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂, Odd (orderOf x)) :
    ¬ 2 ∣ (CFSG.pCore 2 ↥c.L).relIndex
      (CFSG.pCore 2 ↥c.L ⊔ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E : Subgroup ↥c.L := Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂
  let F : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L ⊔ E
  have hEcard : ¬ 2 ∣ Nat.card ↥E := by
    intro h2
    obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hdvd : 2 ∣ orderOf (x : ↥c.L) := by
      rw [Subgroup.orderOf_coe, hx2]
    exact (hEodd (x : ↥c.L) x.2).not_two_dvd_nat hdvd
  have hnormE : E ≤ Subgroup.normalizer (CFSG.pCore 2 ↥c.L : Set ↥c.L) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr
      (inferInstance : (CFSG.pCore 2 ↥c.L).Normal)]
    exact le_top
  have hrel : (CFSG.pCore 2 ↥c.L).relIndex F = Nat.card ↥E := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := E) (K := CFSG.pCore 2 ↥c.L) hnormE).2
    rw [show E ⊔ CFSG.pCore 2 ↥c.L = F from sup_comm E (CFSG.pCore 2 ↥c.L)] at h
    rw [h, hEQ, Subgroup.relIndex_bot_left]
  rw [hrel]
  exact hEcard

private theorem exists_torus_data (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) (hS : KSchurL2) (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hP : IsOmegaPlus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z))
    {z₁ z₂ : ↥c.L} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hz₁ord : orderOf z₁ = r) (hz₂ord : orderOf z₂ = r) (hz₁z₂ : z₁ * z₂ = z₂ * z₁) :
    (c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L) ∧
      (∀ u ∈ Subgroup.zpowers z₁, ∀ v ∈ Subgroup.zpowers z₂, u * v = v * u) ∧
      (∀ x ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂, Odd (orderOf x)) ∧
      ((Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) ⊓ CFSG.pCore 2 ↥c.L = ⊥) ∧
      ¬ 2 ∣ (CFSG.pCore 2 ↥c.L).relIndex
        (CFSG.pCore 2 ↥c.L ⊔ (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂)) := by
  have hCLV := c.inf_centralizer_V_le_pCoreOf hV hK hS hn2 hnat hP
  obtain ⟨hcomm_z, hpow₁, hpow₂⟩ := torus_pow c hr hz₁ord hz₂ord hz₁z₂
  have hEodd := torus_odd c hr hr2 hcomm_z hpow₁ hpow₂
  have hEQ := torus_inf_bot c (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) hEodd
  exact ⟨hCLV, hcomm_z, hEodd, hEQ, torus_index c hEQ hEodd⟩

private theorem exists_w₁ (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (e : Bar2 c.L ≃* ↥(c.H hV))
    (he_mk : ∀ x : ↥c.L, e (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) x) = c.phiL hV x)
    {a b w : MulAut (c.W hV)} (haH : a ∈ c.H hV) (hbH : b ∈ c.H hV) (hwH : w ∈ c.H hV)
    (hwa : w * a * w⁻¹ = a⁻¹) (hwb : w * b * w⁻¹ = b⁻¹) :
    ∃ w₁ : ↥c.L, c.phiL hV w₁ = ⟨w, hwH⟩ ∧
      MulAut.conj (⟨w, hwH⟩ : ↥(c.H hV)) (⟨a, haH⟩ : ↥(c.H hV)) =
        (⟨a, haH⟩ : ↥(c.H hV))⁻¹ ∧
      MulAut.conj (⟨w, hwH⟩ : ↥(c.H hV)) (⟨b, hbH⟩ : ↥(c.H hV)) =
        (⟨b, hbH⟩ : ↥(c.H hV))⁻¹ := by
  obtain ⟨w₁, hw₁⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥c.L) (e.symm ⟨w, hwH⟩)
  have hw₁φ : c.phiL hV w₁ = ⟨w, hwH⟩ := by
    rw [← he_mk w₁, hw₁]
    exact MulEquiv.apply_symm_apply e ⟨w, hwH⟩
  have hconjWA : MulAut.conj (⟨w, hwH⟩ : ↥(c.H hV)) (⟨a, haH⟩ : ↥(c.H hV)) =
      (⟨a, haH⟩ : ↥(c.H hV))⁻¹ := by
    rw [MulAut.conj_apply]
    apply Subtype.ext
    simpa using hwa
  have hconjWB : MulAut.conj (⟨w, hwH⟩ : ↥(c.H hV)) (⟨b, hbH⟩ : ↥(c.H hV)) =
      (⟨b, hbH⟩ : ↥(c.H hV))⁻¹ := by
    rw [MulAut.conj_apply]
    apply Subtype.ext
    simpa using hwb
  exact ⟨w₁, hw₁φ, hconjWA, hconjWB⟩

private theorem conj_zpowers (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {a b w : MulAut (c.W hV)} (haH : a ∈ c.H hV) (hbH : b ∈ c.H hV) (hwH : w ∈ c.H hV)
    (hconjWA : MulAut.conj (⟨w, hwH⟩ : ↥(c.H hV)) (⟨a, haH⟩ : ↥(c.H hV)) =
      (⟨a, haH⟩ : ↥(c.H hV))⁻¹)
    (hconjWB : MulAut.conj (⟨w, hwH⟩ : ↥(c.H hV)) (⟨b, hbH⟩ : ↥(c.H hV)) =
      (⟨b, hbH⟩ : ↥(c.H hV))⁻¹)
    {z₁ z₂ : ↥c.L}
    (hφ₁ : c.phiL hV z₁ ∈ Subgroup.zpowers (⟨a, haH⟩ : ↥(c.H hV)))
    (hφ₂ : c.phiL hV z₂ ∈ Subgroup.zpowers (⟨b, hbH⟩ : ↥(c.H hV))) :
    (∀ u ∈ Subgroup.zpowers z₁,
      (⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV u * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹ =
        (c.phiL hV u)⁻¹) ∧
      (∀ v ∈ Subgroup.zpowers z₂,
      (⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV v * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹ =
        (c.phiL hV v)⁻¹) := by
  have hconj_pow : ∀ (x y : ↥(c.H hV)) (n : ℤ), y * x * y⁻¹ = x⁻¹ →
      y * x ^ n * y⁻¹ = (x ^ n)⁻¹ := by
    intro x y n h
    rw [← MulAut.conj_apply, map_zpow,
      show MulAut.conj y x = x⁻¹ from by rw [MulAut.conj_apply]; exact h, inv_zpow]
  have hconj_z₁ : ∀ u ∈ Subgroup.zpowers z₁,
      (⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV u * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹ =
        (c.phiL hV u)⁻¹ := by
    intro u hu
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [map_zpow]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hφ₁
    rw [← hn, ← zpow_mul]
    exact hconj_pow _ _ _ hconjWA
  have hconj_z₂ : ∀ v ∈ Subgroup.zpowers z₂,
      (⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV v * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹ =
        (c.phiL hV v)⁻¹ := by
    intro v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [map_zpow]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hφ₂
    rw [← hn, ← zpow_mul]
    exact hconj_pow _ _ _ hconjWB
  exact ⟨hconj_z₁, hconj_z₂⟩

private theorem conj_sup (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {w : MulAut (c.W hV)} (hwH : w ∈ c.H hV) {z₁ z₂ : ↥c.L}
    (hcomm_z : ∀ u ∈ Subgroup.zpowers z₁, ∀ v ∈ Subgroup.zpowers z₂, u * v = v * u)
    (hconj_z₁ : ∀ u ∈ Subgroup.zpowers z₁,
      (⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV u * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹ =
        (c.phiL hV u)⁻¹)
    (hconj_z₂ : ∀ v ∈ Subgroup.zpowers z₂,
      (⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV v * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹ =
        (c.phiL hV v)⁻¹) :
    ∀ e ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂,
      (⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV e * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹ =
        (c.phiL hV e)⁻¹ := by
  intro e he
  obtain ⟨u, hu, v, hv, huv⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm_z he
  have hcommuv : Commute (c.phiL hV u) (c.phiL hV v) := by
    show c.phiL hV u * c.phiL hV v = c.phiL hV v * c.phiL hV u
    rw [← map_mul, ← map_mul]
    exact congrArg (c.phiL hV) (hcomm_z u hu v hv)
  rw [← huv, map_mul]
  calc
    (⟨w, hwH⟩ : ↥(c.H hV)) * (c.phiL hV u * c.phiL hV v) *
        (⟨w, hwH⟩ : ↥(c.H hV))⁻¹ =
      ((⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV u * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹) *
        ((⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV v * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹) := by
          group
    _ = (c.phiL hV u)⁻¹ * (c.phiL hV v)⁻¹ := by rw [hconj_z₁ u hu, hconj_z₂ v hv]
    _ = (c.phiL hV u * c.phiL hV v)⁻¹ := by
          rw [mul_inv_rev]
          exact hcommuv.inv_inv.eq

private theorem exists_inverter_conj (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (e : Bar2 c.L ≃* ↥(c.H hV))
    (he_mk : ∀ x : ↥c.L, e (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) x) = c.phiL hV x)
    {a b w : MulAut (c.W hV)} (haH : a ∈ c.H hV) (hbH : b ∈ c.H hV) (hwH : w ∈ c.H hV)
    (hwa : w * a * w⁻¹ = a⁻¹) (hwb : w * b * w⁻¹ = b⁻¹) {z₁ z₂ : ↥c.L}
    (hcomm_z : ∀ u ∈ Subgroup.zpowers z₁, ∀ v ∈ Subgroup.zpowers z₂, u * v = v * u)
    (hφ₁ : c.phiL hV z₁ ∈ Subgroup.zpowers (⟨a, haH⟩ : ↥(c.H hV)))
    (hφ₂ : c.phiL hV z₂ ∈ Subgroup.zpowers (⟨b, hbH⟩ : ↥(c.H hV))) :
    ∃ w₁ : ↥c.L, c.phiL hV w₁ = ⟨w, hwH⟩ ∧
      ∀ e ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂,
        (⟨w, hwH⟩ : ↥(c.H hV)) * c.phiL hV e * (⟨w, hwH⟩ : ↥(c.H hV))⁻¹ =
          (c.phiL hV e)⁻¹ := by
  obtain ⟨w₁, hw₁φ, hconjWA, hconjWB⟩ := exists_w₁ c hV e he_mk haH hbH hwH hwa hwb
  obtain ⟨hconj_z₁, hconj_z₂⟩ :=
    conj_zpowers c hV haH hbH hwH hconjWA hconjWB hφ₁ hφ₂
  exact ⟨w₁, hw₁φ, conj_sup c hV hwH hcomm_z hconj_z₁ hconj_z₂⟩

theorem exists_omegaPlusTorus (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (hA : KTab23a) (hK : KOrdNatural) (hS : KSchurL2) (hKP : KOmPlus)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hP : IsOmegaPlus (c.H hV) 4 (CFSG.Open.pRank 2 D.Z))
    (hNat : NatOmegaPlus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) :
    ∃ r a b t, OmegaPlusTorus c r a b t := by
  obtain ⟨r, a, b, w, hr, hr2, hafix', hbnorm', hbmove', hwmove', hwsq, hwa, hwb, haT,
    haH, hbH, hwH, haord, hbord, hab, hnat⟩ :=
    exists_module_data c hV h4 h1930 hA hK hS hKP hn2 hP hNat
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact r.Prime := ⟨hr⟩
  let e : Bar2 c.L ≃* ↥(c.H hV) := c.e₀ hV hK hS hn2 hnat hP
  have he_mk : ∀ x : ↥c.L, e (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) x) = c.phiL hV x :=
    fun x => c.e₀_mk hV hK hS hn2 hnat hP x
  have hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L :=
    c.ker_phiL_of_omegaPlus hV hK hS hn2 hnat hP
  obtain ⟨z₁, z₂, hz₁ne, hz₁ord, hφ₁, haz, hz₂comm, hz₂ord, hφ₂, hbM, hbNotCent⟩ :=
    exists_lift_torus c hV h4 h1930 e he_mk haH hbH hab hr hr2 haord hbord hafix' hbnorm'
      hbmove' hker
  obtain ⟨hCLV, hcomm_z, hEodd, hEQ, hodd⟩ :=
    exists_torus_data c hV hK hS hn2 hnat hP hr hr2 hz₁ord hz₂ord hz₂comm.symm
  obtain ⟨w₁, hw₁φ, hconjE⟩ :=
    exists_inverter_conj c hV e he_mk haH hbH hwH hwa hwb hcomm_z hφ₁ hφ₂
  obtain ⟨hYodd, hQY, hYle, hQY_eq⟩ :=
    Y_facts c hV hker hwH hw₁φ hconjE (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) hEodd
  obtain ⟨r₀, hr₀, hYeq⟩ := exists_conj_complement c hEQ hQY hYle hQY_eq hodd
  obtain ⟨tL, htL, htφ⟩ := exists_tL c hV hker hr₀ hwH hw₁φ
  have ht_inv : ∀ z ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂, tL * z * tL⁻¹ = z⁻¹ :=
    tL_inv c hV hker hEQ htL hYeq hwH hconjE htφ
  obtain ⟨j, hj⟩ := orderOf_pow_two c hV hwH hwsq hker htφ
  have htM : (tL : G) ∉ D.M := tL_not_mem_M c hV h4 h1930 hwH hwmove' htφ
  have hpermutes : Permutes (Subgroup.zpowers (z₁ : G)) D.T :=
    permutes_lift c hV hCLV haH hr hr2 haord haT hz₁ne hz₁ord hker hφ₁
  exact exists_omegaPlusTorus_of_data c hr hr2 hz₁ord hz₂ord hz₂comm.symm haz hbM hbNotCent
    htM hj ht_inv hpermutes

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
