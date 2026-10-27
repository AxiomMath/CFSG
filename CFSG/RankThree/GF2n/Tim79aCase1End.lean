module

public import CFSG.RankThree.GF2n.Tim78Abelian
public import CFSG.RankThree.GF2n.Tim79aTIWeakClosure
public import CFSG.RankThree.GF2n.Tim79aSec23Cp

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

private theorem inv_mul_commute_of_conj_eq {G : Type*} [Group G] {W : Subgroup G} {t v : G}
    (h : ∀ w ∈ W, t * w * t⁻¹ = v * w * v⁻¹) {w : G} (hw : w ∈ W) :
    v⁻¹ * t * w = w * (v⁻¹ * t) := by
  have h1 : t * w = v * w * v⁻¹ * t := by
    calc t * w = t * w * t⁻¹ * t := by group
      _ = v * w * v⁻¹ * t := by rw [h w hw]
  calc v⁻¹ * t * w = v⁻¹ * (t * w) := by group
    _ = v⁻¹ * (v * w * v⁻¹ * t) := by rw [h1]
    _ = w * (v⁻¹ * t) := by group

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem pCap_wOf_le_V
    (hF1 : ∀ t ∈ P, (∀ w ∈ wOf V H, t * t * w = w * (t * t)) →
      ∃ v ∈ V, ∀ w ∈ wOf V H, t * w * t⁻¹ = v * w * v⁻¹) :
    P ⊓ wOf V H ≤ V := by
  have hinv : ∀ t ∈ P, t * t = 1 → ∀ e ∈ P ⊓ wOf V H, e * t = t * e := by
    intro t htP ht2 e he
    obtain ⟨v, hvV, hv⟩ := hF1 t htP (fun w _ => by rw [ht2, one_mul, mul_one])
    have hve : v * e = e * v := hc.commute_of_mem_P (Subgroup.mem_inf.1 he).1 hvV
    have hce := inv_mul_commute_of_conj_eq hv (Subgroup.mem_inf.1 he).2
    calc e * t = e * (v * (v⁻¹ * t)) := by group
      _ = (e * v) * (v⁻¹ * t) := by group
      _ = (v * e) * (v⁻¹ * t) := by rw [hve]
      _ = v * (e * (v⁻¹ * t)) := by group
      _ = v * (v⁻¹ * t * e) := by rw [hce]
      _ = t * e := by group
  set L : Subgroup G := Subgroup.closure {t | t ∈ P ∧ t * t = 1}
  have hLP : L ≤ P := (Subgroup.closure_le _).2 fun t ht => ht.1
  have hLE : L ≤ Subgroup.centralizer ((P ⊓ wOf V H : Subgroup G) : Set G) :=
    (Subgroup.closure_le _).2 fun t ht =>
      Subgroup.mem_centralizer_iff.2 fun e he => hinv t ht.1 ht.2 e he
  have hVL : V ≤ L := fun v hv =>
    Subgroup.subset_closure ⟨hc.V_le_P hv, hc.elemAb.mul_self_eq_one hv⟩
  have hEL : P ⊓ wOf V H ≤ L := fun e he =>
    Subgroup.subset_closure ⟨(Subgroup.mem_inf.1 he).1,
      hc.wOf_isElemAbelian.mul_self_eq_one (Subgroup.mem_inf.1 he).2⟩
  set U : Subgroup G := L ⊓ Subgroup.centralizer (L : Set G)
  have hVU : V ≤ U := fun v hv => Subgroup.mem_inf.2 ⟨hVL hv,
    Subgroup.mem_centralizer_iff.2 fun l hl => (hc.commute_of_mem_P (hLP hl) hv).symm⟩
  have hEU : P ⊓ wOf V H ≤ U := fun e he => Subgroup.mem_inf.2 ⟨hEL he,
    Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_iff.1 (hLE hl) e he).symm⟩
  have hUc : IsMulCommutative U :=
    ⟨⟨fun x y => Subtype.ext (Subgroup.mem_centralizer_iff.1
      (Subgroup.mem_inf.1 y.2).2 x (Subgroup.mem_inf.1 x.2).1)⟩⟩
  have hQM : Q ≤ M := hc.hQ ▸ (inSubgroup_pCore_two M).2.1
  have hUM : U ≤ M := fun u hu =>
    hQM (hc.P_le_Q (hLP (Subgroup.mem_inf.1 hu).1))
  have hconj : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
    intro m hm l hl
    induction hl using Subgroup.closure_induction with
    | mem t ht =>
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hc.M_le_normalizer_P hm) t).1 ht.1
      · calc m * t * m⁻¹ * (m * t * m⁻¹) = m * (t * t) * m⁻¹ := by group
          _ = 1 := by rw [ht.2]; group
    | one => simpa using L.one_mem
    | mul a b _ _ iha ihb =>
      have : m * (a * b) * m⁻¹ = m * a * m⁻¹ * (m * b * m⁻¹) := by group
      rw [this]
      exact L.mul_mem iha ihb
    | inv a _ iha =>
      have : m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹ := by group
      rw [this]
      exact L.inv_mem iha
  have hMU : M ≤ Subgroup.normalizer (U : Set G) := by
    intro m hm
    have hL' : m ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mem_normalizer_iff.2 fun x => ⟨hconj m hm x, fun hx => by
        simpa [mul_assoc] using hconj m⁻¹ (M.inv_mem hm) _ hx⟩
    exact mem_normalizer_inf hL' (mem_normalizer_centralizer hL')
  exact fun e he => hc.maxAb.2 ⟨hUM, hMU, hUc⟩ hVU (hEU he)

theorem sq_central_of_mem_P
    (hF1 : ∀ t ∈ P, (∀ w ∈ wOf V H, t * t * w = w * (t * t)) →
      ∃ v ∈ V, ∀ w ∈ wOf V H, t * w * t⁻¹ = v * w * v⁻¹)
    (hA6 : ∀ v ∈ V, v ∉ wOf V H → ∀ w ∈ wOf V H, v * w = w * v → w ∈ P) :
    ∀ x ∈ P, ∀ w ∈ wOf V H, x * x * w = w * (x * x) := by
  intro x hxP
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hc.isPGroup_P⟩
  have hsqF : (⟨x, hxP⟩ : P) ^ 2 ∈ frattini ↥P :=
    CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥P) (p := 2) _
  have hxV : x * x ∈ V := hc.frattini_P_le ⟨_, hsqF, by simp [pow_two]⟩
  by_cases hxW : x * x ∈ wOf V H
  · exact fun w hw => hc.wOf_isElemAbelian.comm hxW hw
  · have hC : wOf V H ⊓ Subgroup.centralizer ({x} : Set G) =
        wOf V H ⊓ Subgroup.centralizer ({x ^ 2} : Set G) := by
      ext w
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      refine and_congr_right fun hw => ⟨fun h => ?_, fun h => ?_⟩
      · exact Commute.pow_right (show Commute w x from h) 2
      · have hwP : w ∈ P := hA6 (x * x) hxV hxW w hw (by rw [← pow_two]; exact h.symm)
        exact hc.commute_of_mem_P hxP (hc.pCap_wOf_le_V hF1 (Subgroup.mem_inf.2 ⟨hwP, hw⟩))
    obtain ⟨k, hk⟩ := hc.isPGroup_P ⟨x, hxP⟩
    have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcent := Tim78.tim78_2_1 hc.wOf_isElemAbelian.1
      (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian)
      (H_le_normalizer_wOf V H (hc.PleH hxP)) ⟨k, hxk⟩ hC
    intro w hw
    have hxw : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 (hcent hw)
    calc x * x * w = x * (x * w) := by group
      _ = x * (w * x) := by rw [← hxw]
      _ = x * w * x := by group
      _ = w * x * x := by rw [← hxw]
      _ = w * (x * x) := by group

theorem eq_V_of_dec (hdec : ∀ x ∈ P, ∃ v ∈ V, ∃ c ∈ cPbar V H P, x = v * c) : P = V := by
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    obtain ⟨v₁, hv₁, c₁, hc₁, rfl⟩ := hdec x hx
    obtain ⟨v₂, hv₂, c₂, hc₂, rfl⟩ := hdec y hy
    have h12 : c₁ * c₂ = c₂ * c₁ := by
      have h := Subgroup.commutator_mem_commutator hc₁ hc₂
      rw [hc.commutator_cPbar_eq_bot, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at h
      exact h
    have h1 : v₁ * c₂ = c₂ * v₁ := hc.commute_of_mem_P (Subgroup.mem_inf.1 hc₂).1 hv₁
    have h2 : v₂ * c₁ = c₁ * v₂ := hc.commute_of_mem_P (Subgroup.mem_inf.1 hc₁).1 hv₂
    have h3 : v₁ * v₂ = v₂ * v₁ := hc.elemAb.comm hv₁ hv₂
    calc v₁ * c₁ * (v₂ * c₂) = v₁ * (c₁ * v₂) * c₂ := by group
      _ = v₁ * (v₂ * c₁) * c₂ := by rw [h2]
      _ = v₁ * v₂ * (c₁ * c₂) := by group
      _ = v₂ * v₁ * (c₂ * c₁) := by rw [h3, h12]
      _ = v₂ * (v₁ * c₂) * c₁ := by group
      _ = v₂ * (c₂ * v₁) * c₁ := by rw [h1]
      _ = v₂ * c₂ * (v₁ * c₁) := by group
  refine le_antisymm (fun x hx => ?_) hc.V_le_P
  have hxc : x ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => hcomm y hy x hx
  rwa [hc.centralizer_P_eq] at hxc

theorem false_of_eq_V (hPV : P = V) : False := by
  have hC : Subgroup.centralizer (V : Set G) = V := hPV ▸ hc.centralizer_P_eq
  have hWC := weaklyClosedIn_normalizer_of_centralizer_eq hc.elemAb hc.ti hC
  rw [hc.normalizer_eq] at hWC
  exact hc.notWC hWC

theorem false_of_dec (hdec : ∀ x ∈ P, ∃ v ∈ V, ∃ c ∈ cPbar V H P, x = v * c) : False :=
  hc.false_of_eq_V (hc.eq_V_of_dec hdec)

theorem eq_V_of_actions
    (hF1 : ∀ t ∈ P, (∀ w ∈ wOf V H, t * t * w = w * (t * t)) →
      ∃ v ∈ V, ∀ w ∈ wOf V H, t * w * t⁻¹ = v * w * v⁻¹)
    (hA6 : ∀ v ∈ V, v ∉ wOf V H → ∀ w ∈ wOf V H, v * w = w * v → w ∈ P)
    (hI1 : ∀ c ∈ H, (∀ w ∈ wOf V H, c * w = w * c) →
      ∀ y ∈ xOf V H, ⁅c, y⁆ ∈ wOf V H) :
    P = V := by
  have hsq := hc.sq_central_of_mem_P hF1 hA6
  refine hc.eq_V_of_dec fun x hxP => ?_
  obtain ⟨v, hvV, hv⟩ := hF1 x hxP (hsq x hxP)
  have hcP : v⁻¹ * x ∈ P := P.mul_mem (P.inv_mem (hc.V_le_P hvV)) hxP
  have hcX : v⁻¹ * x ∈ cX V H :=
    show v⁻¹ * x ∈ H ∧ ∀ y ∈ xOf V H, ⁅v⁻¹ * x, y⁆ ∈ wOf V H from
      ⟨hc.PleH hcP, hI1 _ (hc.PleH hcP) fun w hw => inv_mul_commute_of_conj_eq hv hw⟩
  exact ⟨v, hvV, v⁻¹ * x, Subgroup.mem_inf.2 ⟨hcP, hcX⟩, by group⟩

end MinCex

end CFSG.RankThree.GF2n.Tim79a
