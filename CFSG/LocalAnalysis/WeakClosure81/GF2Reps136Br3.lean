module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Br4
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2LinC
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatA
import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136BridgeNat

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_natural_scalar_unit {L : Subgroup (MulAut W)} {ι K : Type}
    [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} (hirr : IsIrrOn L ⊤ ⊥)
    (hreal : (FFModel.nat Γ).Realizes L ⊤ ⊥) {c : K} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    ∃ ψ : ↥(LEnd L), ψ ^ 3 = 1 ∧ ψ ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [FFModel.Realizes] at hreal
  obtain ⟨π, hπ⟩ := hreal
  rw [FFModel.RealizesVia] at hπ
  obtain ⟨hπsurj, hπ2⟩ := hπ
  obtain ⟨-, -, -, -, -, -, β, hβsurj, hβker, hβeq⟩ := hπ2
  have hβinj : Function.Injective β := by
    intro u v huv
    have h1 : β (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h2 : ((u * v⁻¹ : ↥(⊤ : Subgroup W)) : W) ∈ (⊥ : Subgroup W) :=
      (hβker (u * v⁻¹)).mp h1
    rw [Subgroup.mem_bot] at h2
    have h3 : u * v⁻¹ = 1 := Subtype.ext h2
    calc u = u * v⁻¹ * v := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = 1 * v := by rw [h3]
      _ = v := one_mul v
  let q : (↥(FFModel.nat Γ).sec ⧸
        (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec) ≃* ↥(FFModel.nat Γ).sec :=
    (QuotientGroup.quotientMulEquivOfEq
        (Subgroup.bot_subgroupOf (FFModel.nat Γ).sec)).trans
      QuotientGroup.quotientBot
  have q_mk : ∀ m : ↥(FFModel.nat Γ).sec, q (QuotientGroup.mk m) = m := by
    intro m
    change QuotientGroup.quotientBot
        (QuotientGroup.quotientMulEquivOfEq
          (Subgroup.bot_subgroupOf (FFModel.nat Γ).sec)
          (QuotientGroup.mk m)) = m
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    change QuotientGroup.kerLift (MonoidHom.id ↥(FFModel.nat Γ).sec)
        (QuotientGroup.mk m) = m
    rw [QuotientGroup.kerLift_mk]
    rfl
  let f : W →* Multiplicative (ι → K) :=
    { toFun := fun w => (q (β ⟨w, Subgroup.mem_top w⟩) : (FFModel.nat Γ).Amb)
      map_one' := by
        show (q (β ⟨1, Subgroup.mem_top _⟩) : (FFModel.nat Γ).Amb) = 1
        have h1 : (⟨1, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) = 1 := rfl
        rw [h1, map_one, map_one]
        rfl
      map_mul' := by
        intro a b
        show (q (β ⟨a * b, Subgroup.mem_top _⟩) : (FFModel.nat Γ).Amb) =
          (q (β ⟨a, Subgroup.mem_top _⟩) : (FFModel.nat Γ).Amb) *
            (q (β ⟨b, Subgroup.mem_top _⟩) : (FFModel.nat Γ).Amb)
        have hAB : (⟨a * b, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
            ⟨a, Subgroup.mem_top _⟩ * ⟨b, Subgroup.mem_top _⟩ := rfl
        rw [hAB, map_mul, map_mul]
        rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hab1 : q (β ⟨a, Subgroup.mem_top a⟩) = q (β ⟨b, Subgroup.mem_top b⟩) :=
        Subtype.coe_injective hab
      have hab2 : β ⟨a, Subgroup.mem_top a⟩ = β ⟨b, Subgroup.mem_top b⟩ :=
        q.injective hab1
      have hab3 : (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup W)) =
          ⟨b, Subgroup.mem_top b⟩ := hβinj hab2
      exact congrArg Subtype.val hab3
    · intro y
      obtain ⟨u, hu⟩ := hβsurj (q.symm ⟨y, Subgroup.mem_top y⟩)
      refine ⟨(u : W), ?_⟩
      change (q (β ⟨(u : W), Subgroup.mem_top (u : W)⟩) : (FFModel.nat Γ).Amb) = y
      have hu' : (⟨(u : W), Subgroup.mem_top (u : W)⟩ : ↥(⊤ : Subgroup W)) = u := rfl
      rw [hu', hu]
      rfl
  let e : W ≃* Multiplicative (ι → K) := MulEquiv.ofBijective f hf
  have hcardW : Nat.card W = Nat.card K ^ Fintype.card ι := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd (α := ι → K)),
      Nat.card_fun]
    simp only [Nat.card_eq_fintype_card]
  have hWlt : 1 < Nat.card W := by
    have htop : 1 < Nat.card ↥(⊤ : Subgroup W) :=
      (Subgroup.one_lt_card_iff_ne_bot (⊤ : Subgroup W)).mpr (ne_of_gt hirr.1)
    rwa [Subgroup.card_top] at htop
  have e_apply : ∀ (u : ↥(⊤ : Subgroup W)) (m : ↥(FFModel.nat Γ).sec),
      β u = QuotientGroup.mk m → e (u : W) = (m : (FFModel.nat Γ).Amb) := by
    intro u m hm
    change (q (β ⟨(u : W), Subgroup.mem_top (u : W)⟩) : (FFModel.nat Γ).Amb) =
      (m : (FFModel.nat Γ).Amb)
    have hu : (⟨(u : W), Subgroup.mem_top (u : W)⟩ : ↥(⊤ : Subgroup W)) = u := rfl
    rw [hu, hm, q_mk m]
  have e_equiv : ∀ (γ : ↥Γ) (w : Additive W),
      e (((π γ : ↥L) : MulAut W) (Additive.toMul w)) =
        natAct Γ γ (e (Additive.toMul w)) := by
    intro γ w
    let u : ↥(⊤ : Subgroup W) := ⟨Additive.toMul w, Subgroup.mem_top _⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hm' : β u = QuotientGroup.mk m := hm.symm
    have he1 : e (Additive.toMul w) = (m : (FFModel.nat Γ).Amb) := by
      have := e_apply u m hm'
      simpa only [u, Subtype.coe_mk] using this
    have hstep : β ⟨((π γ : ↥L) : MulAut W) (Additive.toMul w), Subgroup.mem_top _⟩ =
        QuotientGroup.mk
          ⟨(FFModel.nat Γ).act γ (m : (FFModel.nat Γ).Amb), Subgroup.mem_top _⟩ := by
      have h := hβeq γ u m (Subgroup.mem_top _) (Subgroup.mem_top _) hm'
      simpa only [u, Subtype.coe_mk] using h
    have he2 : e (((π γ : ↥L) : MulAut W) (Additive.toMul w)) =
        ((FFModel.nat Γ).act γ (m : (FFModel.nat Γ).Amb) : Multiplicative (ι → K)) := by
      have := e_apply
        ⟨((π γ : ↥L) : MulAut W) (Additive.toMul w), Subgroup.mem_top _⟩
        ⟨(FFModel.nat Γ).act γ (m : (FFModel.nat Γ).Amb), Subgroup.mem_top _⟩ hstep
      simpa only [Subtype.coe_mk] using this
    rw [he2, he1]
    rfl
  let eA : Additive W ≃+ (ι → K) := MulEquiv.toAdditiveLeft e
  let sc : K → (ι → K) →+ (ι → K) := fun c =>
    { toFun := fun x => c • x
      map_zero' := smul_zero c
      map_add' := fun x y => smul_add c x y }
  have sc_apply : ∀ (c : K) (x : ι → K), sc c x = c • x := fun c x => rfl
  have eA_equiv : ∀ (γ : ↥Γ) (w : Additive W),
      eA (Additive.ofMul (((π γ : ↥L) : MulAut W) (Additive.toMul w))) =
        (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)).mulVec (eA w) := by
    intro γ w
    change Multiplicative.toAdd (e (((π γ : ↥L) : MulAut W) (Additive.toMul w))) =
      (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)).mulVec
        (Multiplicative.toAdd (e (Additive.toMul w)))
    rw [e_equiv γ w]
    rfl
  let Φ : K → AddMonoid.End (Additive W) := fun c =>
    eA.symm.toAddMonoidHom.comp ((sc c).comp eA.toAddMonoidHom)
  have Φ_apply : ∀ (c : K) (x : Additive W), Φ c x = eA.symm ((sc c) (eA x)) := by
    intro c x
    rfl
  have hmem : ∀ c : K, Φ c ∈ LEnd L := by
    intro c g hg w
    change eA.symm ((sc c) (eA (Additive.ofMul (g (Additive.toMul w))))) =
      Additive.ofMul (g (Additive.toMul (eA.symm ((sc c) (eA w)))))
    apply eA.injective
    rw [AddEquiv.apply_symm_apply]
    obtain ⟨γ, hγ⟩ := hπsurj ⟨g, hg⟩
    have hg' : ((π γ : ↥L) : MulAut W) = g := by
      simpa using congrArg (fun z : ↥L => (z : MulAut W)) hγ
    rw [← hg', eA_equiv γ w, eA_equiv γ (eA.symm ((sc c) (eA w))),
      AddEquiv.apply_symm_apply, sc_apply, sc_apply]
    exact (Matrix.mulVec_smul _ c _).symm
  let φ : K → ↥(LEnd L) := fun c => ⟨Φ c, hmem c⟩
  have hφinj : Function.Injective φ := by
    intro c c' hcc
    have hx : ∀ x : Additive W, eA.symm ((sc c) (eA x)) = eA.symm ((sc c') (eA x)) := by
      intro x
      have h := congrArg (fun ψ : ↥(LEnd L) => ψ.1 x) hcc
      show eA.symm ((sc c) (eA x)) = eA.symm ((sc c') (eA x))
      exact h
    have hneι : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      haveI : IsEmpty ι := h
      have hzero : Fintype.card ι = 0 := Fintype.card_eq_zero_iff.mpr h
      have h1 : Nat.card W = 1 := by rw [hcardW, hzero, pow_zero]
      exact absurd hWlt (not_lt_of_ge (le_of_eq h1))
    obtain ⟨i⟩ := hneι
    have hsc : ∀ d : K,
        (sc d) (eA (eA.symm (Function.const ι (1 : K)))) = Function.const ι d := by
      intro d
      rw [AddEquiv.apply_symm_apply, sc_apply]
      funext j
      simp
    have hx0 := hx (eA.symm (Function.const ι (1 : K)))
    rw [hsc c, hsc c'] at hx0
    have hconst : Function.const ι c = Function.const ι c' := by
      have h := congrArg eA hx0
      rwa [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h
    exact congrFun hconst i
  have Φ_one : Φ 1 = 1 := by
    apply AddMonoidHom.ext
    intro x
    change (Φ 1) x = x
    rw [Φ_apply, sc_apply, one_smul, AddEquiv.symm_apply_apply]
  have Φ_mul : ∀ c c' : K, Φ c * Φ c' = Φ (c * c') := by
    intro c c'
    apply AddMonoidHom.ext
    intro x
    change (Φ c) ((Φ c') x) = (Φ (c * c')) x
    rw [Φ_apply, Φ_apply, Φ_apply, sc_apply, sc_apply, sc_apply, AddEquiv.apply_symm_apply,
      smul_smul]
  refine ⟨⟨Φ c, hmem c⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subring.coe_pow, Subring.coe_one, pow_succ, pow_two]
    calc (Φ c * Φ c) * Φ c = Φ (c * c) * Φ c := by rw [Φ_mul]
      _ = Φ ((c * c) * c) := by rw [Φ_mul]
      _ = Φ (c ^ 3) := by rw [pow_succ, pow_two]
      _ = Φ 1 := by rw [hc3]
      _ = 1 := Φ_one
  · intro h
    have hΦc : Φ c = 1 := congrArg Subtype.val h
    have h1 : φ c = φ 1 := by
      apply Subtype.ext
      change Φ c = Φ 1
      rw [hΦc, Φ_one]
    exact hc1 (hφinj h1)

private theorem w1369_three_dvd_lend_aux {L : Subgroup (MulAut W)} (hfield : IsField ↥(LEnd L))
    {φ : ↥(LEnd L)} (hφ3 : φ ^ 3 = 1) (hφ1 : φ ≠ 1) {k : ℕ}
    (hk : Nat.card ↥(LEnd L) = 2 ^ k) : 3 ∣ 2 ^ k - 1 := by
  letI : Field ↥(LEnd L) := hfield.toField
  have hφ0 : φ ≠ 0 := by
    intro h0
    have h1 : (0 : ↥(LEnd L)) = 1 := by
      have h2 := hφ3
      rw [h0] at h2
      simpa using h2
    exact zero_ne_one h1
  let u := Units.mk0 φ hφ0
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    change ((u : ↥(LEnd L)) ^ 3) = 1
    rw [show (u : ↥(LEnd L)) = φ from Units.val_mk0 hφ0, hφ3]
  have hu1 : u ≠ 1 := by
    intro hh
    apply hφ1
    have h' : (u : ↥(LEnd L)) = (1 : ↥(LEnd L)) := by rw [hh]; rfl
    simpa [u] using h'
  have huord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdiv := orderOf_dvd_natCard u
  rw [huord] at hdiv
  have hcardU := Nat.card_units (↥(LEnd L))
  rw [hcardU, hk] at hdiv
  exact hdiv

private theorem w1369_mQuot_eq_rk_map_mk_aux (C V : Subgroup W) :
    E3.mQuot V C = rk ↥(V.map (QuotientGroup.mk' C)) := by
  have h := Subgroup.relIndex_ker (QuotientGroup.mk' C : W →* W ⧸ C) (K := V)
  rw [QuotientGroup.ker_mk'] at h
  rw [E3.mQuot, rk, h]

private theorem w1369_tcost_le_rk (t : MulAut W) (L : Subgroup (MulAut W)) :
    tcost t L (Wd L) ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
  let X := commSub (Wd L) (Subgroup.zpowers t)
  have hXA : X ≤ commSub ⊤ (Subgroup.zpowers t) := commSub_mono le_top le_rfl
  have hCmap : (Cd L).map (QuotientGroup.mk' (Cd L)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨y, hy, rfl⟩
    rw [Subgroup.mem_bot]
    exact MonoidHom.mem_ker.mp (by rwa [QuotientGroup.ker_mk'])
  calc tcost t L (Wd L)
      = E3.mQuot (X ⊔ Cd L) (Cd L) := rfl
    _ = rk ↥((X ⊔ Cd L).map (QuotientGroup.mk' (Cd L))) :=
        w1369_mQuot_eq_rk_map_mk_aux (Cd L) (X ⊔ Cd L)
    _ = rk ↥(X.map (QuotientGroup.mk' (Cd L))) := by
        rw [Subgroup.map_sup, hCmap, sup_bot_eq]
    _ ≤ rk ↥X := padicValNat_two_le_of_dvd (card_subgroup_pos X).ne'
        (Subgroup.card_map_dvd (H := X) (QuotientGroup.mk' (Cd L)))
    _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := rk_mono hXA

private theorem w1369_exp_eq {m a k n d : ℕ} (ha2 : 2 ≤ a) (ham : a ≤ m) (hm3 : m ≤ 3)
    (hak : a ≤ k) (hd2 : 2 ≤ d) (hrk : a * n = k * d) (hn2 : 2 ≤ n)
    (hcase : (∃ r : ℕ, 1 ≤ r ∧ m = k * r) ∨ (Even k ∧ a * n = 2 * m))
    (h3 : a = 2 → 3 ∣ 2 ^ k - 1) : m = a ∨ (a = 2 ∧ n = 3 ∧ m = 3) := by
  have hk3 : k ≤ 3 := by
    rcases hcase with ⟨r, hr1, hm⟩ | ⟨-, hrk2⟩
    · calc k = k * 1 := (mul_one k).symm
        _ ≤ k * r := Nat.mul_le_mul_left k hr1
        _ = m := hm.symm
        _ ≤ 3 := hm3
    · have h : k * d = 2 * m := by rw [← hrk]; exact hrk2
      have h2 : 2 * k ≤ 2 * m := by
        calc 2 * k = k * 2 := by rw [Nat.mul_comm]
          _ ≤ k * d := Nat.mul_le_mul_left k hd2
          _ = 2 * m := h
      omega
  have hka : k = a := by
    rcases lt_or_eq_of_le hak with hlt | heq
    · have ha2' : a = 2 := by omega
      have hk3' : k = 3 := by omega
      have hd := h3 ha2'
      rw [hk3'] at hd
      exact absurd hd (by norm_num)
    · exact heq.symm
  rcases hcase with ⟨r, hr1, hm⟩ | ⟨hkeven, hrk2⟩
  · left
    have hr : r = 1 := by
      by_contra hr
      have hr2 : 2 ≤ r := by omega
      have h4 : 2 * a ≤ a * r := by
        calc 2 * a = a * 2 := by rw [Nat.mul_comm]
          _ ≤ a * r := Nat.mul_le_mul_left a hr2
      rw [hka] at hm
      omega
    rw [hka, hr, mul_one] at hm
    exact hm
  · rw [hka] at hkeven
    by_cases ha4 : 4 ≤ a
    · have h8 : 8 ≤ a * n := by
        calc 8 = 4 * 2 := by norm_num
          _ ≤ a * n := Nat.mul_le_mul ha4 hn2
      omega
    · have ha2' : a = 2 := by
        obtain ⟨c, hc⟩ := hkeven
        omega
      have hnm : n = m := by
        rw [ha2'] at hrk2
        omega
      by_cases hn3 : n = 3
      · exact Or.inr ⟨ha2', hn3, by omega⟩
      · exact Or.inl (by omega)

theorem row1_exact (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (c : Ctx136 Y t L) (hf : FaithOn L (Wd L) (Cd L))
    (hirr : IsIrrOn L (Wd L) (Cd L)) (h : Row1Ineq L (Wd L) (Cd L) (tcost t L (Wd L))) :
    Conc4_135 L (Wd L) (Cd L) (tcost t L (Wd L)) := by
  classical
  obtain ⟨n, a, ha2, ham, hcase⟩ := h
  have hstab : StabPair L (Wd L) (Cd L) := fun x hx => ⟨hirr.2.1 x hx, hirr.2.2.1 x hx⟩
  have hZU : Cd L ≤ Wd L := hirr.1.le
  have hfixL : L.map (MulAut.conj t).toMonoidHom = L := c.hfix L c.comp
  have htU : ∀ u ∈ Wd L, t u ∈ Wd L := by
    intro u hu
    have hmap := Asc81c.commSub_map_conj L t
    rw [hfixL] at hmap
    change t u ∈ commSub ⊤ L
    rw [hmap]
    exact Subgroup.mem_map_of_mem t.toMonoidHom hu
  have htZ : ∀ z ∈ Cd L, t z ∈ Cd L := by
    intro z hz
    obtain ⟨hzU, hzF⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨htU z hzU, ?_⟩
    have hfixV : (fixV L).map t.toMonoidHom = fixV L := by
      have hmap := Asc81c.fixV_map_conj L t
      rw [hfixL] at hmap
      exact hmap.symm
    rw [← hfixV]
    exact Subgroup.mem_map_of_mem t.toMonoidHom hzF
  let Lb : Subgroup (MulAut (Sect (Wd L) (Cd L))) := secSub (Wd L) (Cd L) L
  let tb : MulAut (Sect (Wd L) (Cd L)) := secAut (Wd L) (Cd L) t htU htZ
  have hirrM : IsIrrOn Lb ⊤ ⊥ := (secSub_irr hstab hirr.1).mpr hirr
  have hM2 : ∀ x : Sect (Wd L) (Cd L), x ^ 2 = 1 := sect_exp_two hw2 (Wd L) (Cd L)
  have htNb : ∀ g ∈ Lb, tb * g * tb⁻¹ ∈ Lb := by
    intro g hg
    have hmap := secSub_map_conj hstab htU htZ (t := t)
    rw [hfixL] at hmap
    have hmem : (MulAut.conj tb) g ∈
        Lb.map (MulAut.conj tb).toMonoidHom := Subgroup.mem_map_of_mem _ hg
    rw [hmap] at hmem
    simpa [tb, MulAut.conj_apply] using hmem
  have hcost0 : rk ↥(commSub ⊤ (Subgroup.zpowers tb)) = tcost t L (Wd L) := by
    rw [rk_secAut_comm (Z := Cd L) hZU htU htZ]
  have hm_eq : E3.mQuot ⊤ (fixV (Subgroup.zpowers tb)) = tcost t L (Wd L) := by
    rw [show E3.mQuot ⊤ (fixV (Subgroup.zpowers tb)) = rkIdx (fixV (Subgroup.zpowers tb)) from by
      unfold E3.mQuot rkIdx
      rw [Subgroup.relIndex_top_right]]
    rw [rkIdx_fixV_zpowers, commV_eq_commSub]
    exact hcost0
  have htbm2 : tb ^ 2 = 1 := by
    rw [pow_two]
    ext m
    induction m using QuotientGroup.induction_on with
    | H u =>
      rw [MulAut.mul_apply, MulAut.one_apply, secAut_mk, secAut_mk]
      congr 1
      exact Subtype.ext (by
        have ht2w : t * t = 1 := by
          have hpow := pow_orderOf_eq_one t
          rw [c.std.t2] at hpow
          rwa [pow_two] at hpow
        have h := congrFun (congrArg (fun f : MulAut W => (f : W → W)) ht2w) (u : W)
        simpa [MulAut.mul_apply] using h)
  have htbm1 : tb ≠ 1 := by
    intro h1
    have hfix : fixV (Subgroup.zpowers tb) = ⊤ := by
      rw [h1, Subgroup.zpowers_one_eq_bot]
      exact CFSG.Quasithin.B1.fixV_bot
    have h0 : E3.mQuot ⊤ (fixV (Subgroup.zpowers tb)) = 0 := by
      rw [hfix, E3.mQuot_self]
    rw [hm_eq] at h0
    omega
  have ht2b : orderOf tb = 2 := orderOf_eq_prime htbm2 htbm1
  have hnabL : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcenter : Subgroup.center ↥L = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact Subgroup.mem_center_iff.mpr fun b => Subtype.ext (hcon x x.2 b b.2).symm
    haveI : Subsingleton (↥L ⧸ Subgroup.center ↥L) := by
      rw [hcenter]
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with
      | H x =>
        induction b using QuotientGroup.induction_on with
        | H y =>
          rw [QuotientGroup.eq]
          exact Subgroup.mem_top _
    haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := c.comp.2.2.2
    exact (not_subsingleton_iff_nontrivial.mpr
      (inferInstance : Nontrivial (↥L ⧸ Subgroup.center ↥L))) inferInstance
  have hnab : ∃ a ∈ Lb, ∃ b ∈ Lb, a * b ≠ b * a := by
    obtain ⟨e⟩ := mulEquiv_secSub hstab hf
    obtain ⟨x, hx, y, hy, hxy⟩ := hnabL
    refine ⟨e ⟨x, hx⟩, (e ⟨x, hx⟩).2, e ⟨y, hy⟩, (e ⟨y, hy⟩).2, ?_⟩
    intro h
    apply hxy
    have h1 : e (⟨x, hx⟩ * ⟨y, hy⟩) = e (⟨y, hy⟩ * ⟨x, hx⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h
    have h2 := e.injective h1
    simpa using congrArg Subtype.val h2
  obtain ⟨k, d, -, hk, hd, hcase2⟩ := w135c2_dichotomy hM2 hirrM htNb ht2b
  have hcase2' : (∃ r : ℕ, 1 ≤ r ∧ tcost t L (Wd L) = k * r) ∨
      (Even k ∧ rk (Sect (Wd L) (Cd L)) = 2 * tcost t L (Wd L)) := by
    rcases hcase2 with ⟨r, hr1, hr⟩ | ⟨hev, hrk2⟩
    · exact Or.inl ⟨r, hr1, hm_eq.symm.trans hr⟩
    · exact Or.inr ⟨hev, by rw [hrk2, hm_eq]⟩
  have hm3 : tcost t L (Wd L) ≤ 3 := (w1369_tcost_le_rk t L).trans c.std.cost
  have hd2 : 2 ≤ d := w135c2_one_lt_dim hM2 hirrM hnab hk hd
  have shape_data : ∀ (K : Type) [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]
      (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (hK : Nat.card K = 2 ^ a)
      (hreal : (FFModel.nat Γ).Realizes Lb ⊤ ⊥),
      a ≤ k ∧ rk (Sect (Wd L) (Cd L)) = a * Fintype.card ι ∧
        (a = 2 → 3 ∣ 2 ^ k - 1) := by
    intro K _ _ ι _ _ Γ hK hreal
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨hKE, hcardW⟩ :=
      w135c2_natural_data (W := Sect (Wd L) (Cd L)) (L := Lb) hirrM hreal
    refine ⟨?_, ?_, ?_⟩
    · have h : 2 ^ a ≤ 2 ^ k := by rw [← hK, ← hk]; exact hKE
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
    · refine Nat.pow_right_injective (show 2 ≤ 2 by norm_num) ?_
      change 2 ^ rk (Sect (Wd L) (Cd L)) = 2 ^ (a * Fintype.card ι)
      rw [← w135_card_eq_two_pow_rk hM2, hcardW, hK, ← pow_mul]
    · intro ha2
      have hcardK : Nat.card K = 4 := by rw [hK, ha2]; norm_num
      obtain ⟨c, hc3, hc1⟩ : ∃ c : K, c ^ 3 = 1 ∧ c ≠ 1 := by
        have hcardU : Nat.card Kˣ = 3 := by
          rw [Nat.card_units, hcardK]
        haveI : Fintype Kˣ := Fintype.ofFinite Kˣ
        have hcardF : 1 < Fintype.card Kˣ := by
          rw [← Nat.card_eq_fintype_card, hcardU]; norm_num
        obtain ⟨u, hu⟩ := Fintype.exists_ne_of_one_lt_card hcardF (1 : Kˣ)
        have hdvd : orderOf u ∣ 3 := by
          rw [← hcardU]; exact orderOf_dvd_natCard u
        have hne1 : orderOf u ≠ 1 := fun hh => hu (orderOf_eq_one_iff.mp hh)
        have hord : orderOf u = 3 := by
          rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf u) hdvd with h | h
          · exact absurd h hne1
          · exact h
        refine ⟨(u : K), ?_, ?_⟩
        · have hu3 : u ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one u
          calc (u : K) ^ 3 = ((u ^ 3 : Kˣ) : K) := (Units.val_pow_eq_pow_val u 3).symm
            _ = ((1 : Kˣ) : K) := by rw [hu3]
            _ = 1 := rfl
        · intro hh
          exact hu (Units.ext hh)
      obtain ⟨ψ, hψ3, hψ1⟩ := w1369_natural_scalar_unit hirrM hreal hc3 hc1
      exact w1369_three_dvd_lend_aux (w135c2_lend_isField hM2 hirrM) hψ3 hψ1 hk
  have hmain : a = tcost t L (Wd L) := by
    rcases hcase with ⟨hSL, hnat⟩ | hrest
    · obtain ⟨K, hKfield, hKfin, hKa, hreal0⟩ := hnat
      have hreal : (FFModel.nat (StatedSL n K)).Realizes Lb ⊤ ⊥ :=
        (realizes_secSub_iff (FFModel.nat (StatedSL n K)) hstab hZU hf).mpr hreal0
      obtain ⟨hak, hrk, h3⟩ := shape_data K (Γ := StatedSL n K) hKa hreal
      have hN2 : 2 ≤ Fintype.card (Fin n) := w135c2_two_le_card_index (L := Lb) hreal hnab
      have hcase3 : (∃ r : ℕ, 1 ≤ r ∧ tcost t L (Wd L) = k * r) ∨
          (Even k ∧ a * Fintype.card (Fin n) = 2 * tcost t L (Wd L)) := by
        rcases hcase2' with ⟨r, hr1, hr⟩ | ⟨hev, hrk2⟩
        · exact Or.inl ⟨r, hr1, hr⟩
        · exact Or.inr ⟨hev, by rw [← hrk, hrk2]⟩
      have hrk'' : a * Fintype.card (Fin n) = k * d := by rw [← hrk, hd]
      rcases w1369_exp_eq ha2 ham hm3 hak hd2 hrk'' hN2 hcase3 h3 with
        hm | ⟨ha2e, hN3, hm⟩
      · exact hm.symm
      · exfalso
        have hn3 : n = 3 := by simpa [Fintype.card_fin] using hN3
        rw [hn3] at hSL hreal0
        rw [ha2e] at hSL hKa
        exact sl34_excluded hw2 c hf hirr ⟨hSL, ⟨K, hKfield, hKfin, hKa, hreal0⟩, hm⟩
    · rcases hrest with ⟨hSp, hnat⟩ | hrest
      · obtain ⟨-, K, hKfield, hKfin, hKa, hreal0⟩ := hnat
        have hreal : (FFModel.nat (StatedSp (n / 2) K)).Realizes Lb ⊤ ⊥ :=
          (realizes_secSub_iff (FFModel.nat (StatedSp (n / 2) K)) hstab hZU hf).mpr hreal0
        obtain ⟨hak, hrk, h3⟩ := shape_data K (Γ := StatedSp (n / 2) K) hKa hreal
        have hN2 : 2 ≤ Fintype.card (Fin (n / 2) ⊕ Fin (n / 2)) :=
          w135c2_two_le_card_index (L := Lb) hreal hnab
        have hcase3 : (∃ r : ℕ, 1 ≤ r ∧ tcost t L (Wd L) = k * r) ∨
            (Even k ∧ a * Fintype.card (Fin (n / 2) ⊕ Fin (n / 2)) =
              2 * tcost t L (Wd L)) := by
          rcases hcase2' with ⟨r, hr1, hr⟩ | ⟨hev, hrk2⟩
          · exact Or.inl ⟨r, hr1, hr⟩
          · exact Or.inr ⟨hev, by rw [← hrk, hrk2]⟩
        have hrk'' : a * Fintype.card (Fin (n / 2) ⊕ Fin (n / 2)) = k * d := by
          rw [← hrk, hd]
        rcases w1369_exp_eq ha2 ham hm3 hak hd2 hrk'' hN2 hcase3 h3 with
          hm | ⟨-, hN3, -⟩
        · exact hm.symm
        · exfalso
          have hcard : n / 2 + n / 2 = 3 := by
            simpa only [Fintype.card_sum, Fintype.card_fin] using hN3
          have htwo := Nat.two_mul_div_two_of_even hSp.1
          obtain ⟨c, hc⟩ := hSp.1
          omega
      · rcases hrest with ⟨hOP, hnat⟩ | ⟨hOM, hnat⟩
        · obtain ⟨-, K, hKfield, hKfin, hKa, hreal0⟩ := hnat
          have hreal : (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K))).Realizes
              Lb ⊤ ⊥ :=
            (realizes_secSub_iff
              (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K))) hstab hZU hf).mpr hreal0
          obtain ⟨hak, hrk, h3⟩ := shape_data K
            (Γ := StatedOmega (StatedQuadPlus (n / 2) K)) hKa hreal
          have hN2 : 2 ≤ Fintype.card (Fin (n / 2) ⊕ Fin (n / 2)) :=
            w135c2_two_le_card_index (L := Lb) hreal hnab
          have hcase3 : (∃ r : ℕ, 1 ≤ r ∧ tcost t L (Wd L) = k * r) ∨
              (Even k ∧ a * Fintype.card (Fin (n / 2) ⊕ Fin (n / 2)) =
                2 * tcost t L (Wd L)) := by
            rcases hcase2' with ⟨r, hr1, hr⟩ | ⟨hev, hrk2⟩
            · exact Or.inl ⟨r, hr1, hr⟩
            · exact Or.inr ⟨hev, by rw [← hrk, hrk2]⟩
          have hrk'' : a * Fintype.card (Fin (n / 2) ⊕ Fin (n / 2)) = k * d := by
            rw [← hrk, hd]
          rcases w1369_exp_eq ha2 ham hm3 hak hd2 hrk'' hN2 hcase3 h3 with
            hm | ⟨-, hN3, -⟩
          · exact hm.symm
          · exfalso
            have hcard : n / 2 + n / 2 = 3 := by
              simpa only [Fintype.card_sum, Fintype.card_fin] using hN3
            have htwo := Nat.two_mul_div_two_of_even hOP.1
            obtain ⟨c, hc⟩ := hOP.1
            omega
        · obtain ⟨-, K, hKfield, hKfin, b, cc, hKa, hquad, hreal0⟩ := hnat
          have hreal : (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K b cc))).Realizes
              Lb ⊤ ⊥ :=
            (realizes_secSub_iff
              (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K b cc))) hstab hZU hf).mpr
              hreal0
          obtain ⟨hak, hrk, h3⟩ := shape_data K
            (Γ := StatedOmega (StatedQuadMinus (n / 2) K b cc)) hKa hreal
          have hN2 : 2 ≤ Fintype.card (Fin (n / 2 - 1) ⊕ Fin (n / 2 - 1) ⊕ Fin 2) :=
            w135c2_two_le_card_index (L := Lb) hreal hnab
          have hcase3 : (∃ r : ℕ, 1 ≤ r ∧ tcost t L (Wd L) = k * r) ∨
              (Even k ∧ a * Fintype.card (Fin (n / 2 - 1) ⊕ Fin (n / 2 - 1) ⊕ Fin 2) =
                2 * tcost t L (Wd L)) := by
            rcases hcase2' with ⟨r, hr1, hr⟩ | ⟨hev, hrk2⟩
            · exact Or.inl ⟨r, hr1, hr⟩
            · exact Or.inr ⟨hev, by rw [← hrk, hrk2]⟩
          have hrk'' : a * Fintype.card (Fin (n / 2 - 1) ⊕ Fin (n / 2 - 1) ⊕ Fin 2) = k * d := by
            rw [← hrk, hd]
          rcases w1369_exp_eq ha2 ham hm3 hak hd2 hrk'' hN2 hcase3 h3 with
            hm | ⟨-, hN3, -⟩
          · exact hm.symm
          · exfalso
            have hcard : n / 2 - 1 + (n / 2 - 1 + 2) = 3 := by
              simpa only [Fintype.card_sum, Fintype.card_fin] using hN3
            have htwo := Nat.two_mul_div_two_of_even hOM.1
            obtain ⟨c, hc⟩ := hOM.1
            omega
  rw [hmain] at hcase
  exact Or.inl ⟨n, hcase⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
