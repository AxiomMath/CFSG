module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Index
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Base
public import CFSG.RankThree.GF2n.Stroth80.Sec7IndexOrbit
public import CFSG.RankThree.GF2n.Stroth80.Sec7VtQ
public import CFSG.RankThree.GF2n.Stroth80.Sec7Split72
public import CFSG.RankThree.GF2n.Stroth80.Sec7Orbit72

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Step72NormVStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x : G, x ∈ LB M Q B → x ∉ Z0 →
    ∀ g ∈ M, g ∈ Subgroup.normalizer (LB M Q B : Set G) →
    x * (g * t * g⁻¹)⁻¹ ∈ Q →
    Nat.card ↥(hc.CN t) < Nat.card Z * Nat.card ↥(hc.CN t ⊓ CommQ hc.hyp.Q_normal.2 x) →
    g ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G)

theorem step72NormV_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hZV : Sec7ZVStatement) (hCVs : Sec7CVStatement)
    (hO : Step72OrbitStatement) : Step72NormVStatement := by
  intro G _ _ M Q Z B hc n t hs hno Z0 hZ0 x hxL hxZ g hgM hgN hxg hcount
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have htQ : t ∉ Q := hs.toSec5.notQ
  have hQLB : Q ≤ LB M Q B := le_sup_left
  have hQM : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hQN : Q ≤ hc.CN t := fun y hy => Ctx.mem_CN.mpr
    ⟨hc.Q_le_Rt ht hy, fun v hv => hc.hyp.toHyp79.comm_mem_V hy (hc.Vt_le_Q t hv)⟩
  have hu : g * t * g⁻¹ ∈ LB M Q B := by
    have e : g * t * g⁻¹ = (x * (g * t * g⁻¹)⁻¹)⁻¹ * x := by group
    rw [e]
    exact (LB M Q B).mul_mem (hQLB (Q.inv_mem hxg)) hxL
  have huCN : g * t * g⁻¹ ∈ hc.CN t := stroth72_conj_mem_CN hc hs hno hZ0 hgM hu
  have hVU : Ut Q Z t = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t hs Z0 hZ0 t htZ0 htQ
  have hvan : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z :=
    fun v hv => (Ctx.mem_CN.mp huCN).2 v hv
  have hVg : conjSubgroup g (Vt M (LB M Q B) B Z t) =
      Vt M (LB M Q B) B Z (g * t * g⁻¹) :=
    conjSubgroup_Vt_eq hgM (hc.conj_Z_eq hgM) t
  have hVW : conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
    conj_Vt_le_Wt hc ht hVU.symm hgM hvan
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hd := h52b G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl rfl
  have hCV : conjSubgroup r B ≤ Vt M (LB M Q B) B Z t := by
    intro x' hx'
    have hb : r⁻¹ * x' * r ∈ B := mem_conjSubgroup.mp hx'
    have hbV : r⁻¹ * x' * r ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hb
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hr.mem)
      (r⁻¹ * x' * r)).mp hbV
    have e : r * (r⁻¹ * x' * r) * r⁻¹ = x' := by group
    rwa [e] at h1
  have hÃV : conjSubgroup r B ⊔ Z ≤ Vt M (LB M Q B) B Z t := sup_le hCV sec39_Z_le_Vt
  have hWcent : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ∀ v ∈ Vt M (LB M Q B) B Z t,
      w * v * w⁻¹ = v := fun w hw v hv => by
    have := Subgroup.mem_centralizer_iff.mp hw.2 v hv
    rw [← this]
    group
  have hVnorm : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      w ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer (Vt M (LB M Q B) B Z t : Set G) hw.2
  have hcommu : ∀ y ∈ CommQ hQM x, ⁅y, g * t * g⁻¹⁆ ∈ Q := by
    intro y hy
    obtain ⟨hyM, hyx⟩ := hy
    obtain ⟨q₀, hq₀, hxq⟩ : ∃ q₀ ∈ Q, x = q₀ * (g * t * g⁻¹) :=
      ⟨x * (g * t * g⁻¹)⁻¹, hxg, by group⟩
    have e : ⁅y, g * t * g⁻¹⁆ = (y * q₀ * y⁻¹)⁻¹ * ⁅y, x⁆ * q₀ := by
      rw [hxq]
      simp only [commutatorElement_def]
      group
    rw [e]
    have hyq : y * q₀ * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQM hyM) q₀).mp hq₀
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem hyq) hyx) hq₀
  set Ã : Subgroup G := conjSubgroup r B ⊔ Z with hÃdef
  have hQM' : Q ≤ M := by
    rw [hc.hyp.hQ]
    exact Subgroup.map_subtype_le _
  have hÃM : conjSubgroup r B ⊔ Z ≤ M := by
    refine sup_le ?_ (fun z hz => ?_)
    · intro a ha
      exact hQM' (hc.Vt_le_Q t (hÃV (Subgroup.mem_sup_left ha)))
    · exact hQM' (hc.hyp.Z_normal.left hz)
  have hClaimA : ∀ v ∈ conjSubgroup g (Vt M (LB M Q B) B Z t),
      v ∈ (Wt Q (Vt M (LB M Q B) B Z t) ⊓ QB B) ⊔ Vt M (LB M Q B) B Z t := by
    intro v hv
    by_contra hvn
    obtain ⟨a₁, ha₁, a₂, ha₂, hva⟩ := hd.exists_mul (hVW hv)
    have ha₁' : a₁ ∈ (Wt Q (Vt M (LB M Q B) B Z t) ⊓ QB B) ⊔ Vt M (LB M Q B) B Z t := by
      have e : QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) = Wt Q (Vt M (LB M Q B) B Z t) ⊓ QB B :=
        inf_comm _ _
      rw [← e]
      exact ha₁
    have ha₂V : a₂ ∉ Vt M (LB M Q B) B Z t := by
      intro h
      apply hvn
      rw [hva]
      exact Subgroup.mul_mem _ ha₁' (Subgroup.mem_sup_right h)
    obtain ⟨β, hβ, c₂, hc₂, hdec₂⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (H := QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t))
      (K := Vt M (LB M Q B) B Z t) (fun w hw => hVnorm w hw.2) ha₂
    obtain ⟨α, hα, c₁, hc₁, hdec₁⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (H := QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t))
      (K := Vt M (LB M Q B) B Z t) (fun w hw => hVnorm w hw.2) ha₁
    have hβV : β ∉ Vt M (LB M Q B) B Z t := by
      intro h
      apply ha₂V
      rw [← hdec₂]
      exact Subgroup.mul_mem _ h hc₂
    have hcomm : c₁ * β = β * c₁ := by
      have := hWcent β hβ.2 c₁ hc₁
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    have hvαβ : v = α * β * (c₁ * c₂) := by
      rw [hva, ← hdec₁, ← hdec₂]
      calc α * c₁ * (β * c₂) = α * (c₁ * β) * c₂ := by group
        _ = α * (β * c₁) * c₂ := by rw [hcomm]
        _ = α * β * (c₁ * c₂) := by group
    have hsplit_mem : α * β * (c₁ * c₂) ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
      rw [← hvαβ]
      exact hv
    have hcV : c₁ * c₂ ∈ Vt M (LB M Q B) B Z t := (Vt M (LB M Q B) B Z t).mul_mem hc₁ hc₂
    have hαmem : α ∈ Wt Q (Vt M (LB M Q B) B Z t) ⊓ QB B := ⟨hα.2, hα.1⟩
    have hβmem : β ∈ Wt Q (Vt M (LB M Q B) B Z t) ⊓ QB (conjSubgroup r B) := ⟨hβ.2, hβ.1⟩
    have hexists : ∃ y ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t,
        y ∈ Subgroup.normalizer (conjSubgroup g (Vt M (LB M Q B) B Z t) : Set G) ∧
          ⁅β, y⁆ ∉ Z := by
      by_contra hne
      push Not at hne
      have hcommA : ∀ y ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t,
          ⁅β, y⁆ ∈ conjSubgroup r B ⊔ Z := by
        intro y hy
        have h1 : ⁅y, β⁆ ∈ conjSubgroup r B ⊔ Z :=
          (hc.conj_of_mem hrM).comm_mem_sup_Z_of_mem_LB hy.1 ⟨hβmem.1.1, hβmem.2⟩
        rw [← commutatorElement_inv]
        exact (conjSubgroup r B ⊔ Z).inv_mem h1
      have hZn : ∀ a ∈ conjSubgroup r B ⊔ Z, ∀ z ∈ Z, a * z * a⁻¹ ∈ Z := fun a ha z hz =>
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hÃM ha)) z).mp hz
      have hmul : ∀ y ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t,
          ∀ c' ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t,
          ∃ z ∈ Z, ⁅β, y * c'⁆ = ⁅β, y⁆ * ⁅β, c'⁆ * z := by
        intro y hy c' _
        have haÃ : ⁅β, c'⁆ ∈ conjSubgroup r B ⊔ Z := hcommA c' ‹_›
        have haV : ⁅β, c'⁆ ∈ Vt M (LB M Q B) B Z t := hÃV haÃ
        have haM : ⁅β, c'⁆ ∈ M := hÃM haÃ
        refine ⟨⁅β, c'⁆⁻¹ * ⁅y, ⁅β, c'⁆⁆ * ⁅β, c'⁆, ?_, ?_⟩
        · have hz := (Subgroup.mem_normalizer_iff.mp
            (hc.hyp.Z_normal.2 (M.inv_mem haM)) ⁅y, ⁅β, c'⁆⁆).mp
            ((Ctx.mem_CN.mp hy.2).2 _ haV)
          simpa using hz
        · simp only [commutatorElement_def]
          group
      have hsurj : ∀ a ∈ conjSubgroup r B ⊔ Z,
          ∃ y ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, ∃ z ∈ Z, a = ⁅β, y⁆ * z := by
        intro a ha
        obtain ⟨y, hy, z, hz, hyeq⟩ := hO G M Q Z B hc n t hs r hr β hβmem hβV a ha
        exact ⟨y, hy, z⁻¹, Z.inv_mem hz, by rw [hyeq]; group⟩
      have hC : ∀ c' ∈ (LB M Q (conjSubgroup r B) ⊓ hc.CN t) ⊓ CommQ hQM x,
          ⁅β, c'⁆ ∈ Z := by
        intro c' hc'
        have hcx : c' ∈ CommQ hQM x := hc'.2
        have hnorm : c' ∈ Subgroup.normalizer (conjSubgroup g (Vt M (LB M Q B) B Z t) :
            Set G) := by
          rw [hVg]
          exact mem_normalizer_Vt_of_comm_mem M Q (LB M Q B) B Z hQLB hQM hcx.1
            (hc.conj_Z_eq hcx.1) (hcommu c' hcx)
        exact hne c' hc'.1 hnorm
      have hcnt := index_ge_card_of_orbit (LB M Q (conjSubgroup r B) ⊓ hc.CN t)
        ((LB M Q (conjSubgroup r B) ⊓ hc.CN t) ⊓ CommQ hQM x) (conjSubgroup r B ⊔ Z) Z β
        inf_le_left (le_sup_right) hZn (fun y hy => hcommA y hy) hmul hC hsurj
      have hq : Nat.card Z ≤ Nat.card (Ã ⧸ Z.subgroupOf Ã) := by
        have hcardB : Nat.card (conjSubgroup r B) = Nat.card Z := by
          obtain ⟨g', hg'⟩ := hc.conj
          rw [card_conjSubgroup, hg', card_conjSubgroup]
        have hinter : Z ⊓ conjSubgroup r B = ⊥ := (hc.conj_of_mem hrM).inf_eq_bot
        let f : ↥(conjSubgroup r B) → (Ã ⧸ Z.subgroupOf Ã) :=
          fun c => QuotientGroup.mk ⟨(c : G), Subgroup.mem_sup_left c.2⟩
        have hf : Function.Injective f := by
          intro c c' hcc
          have h1 := QuotientGroup.eq.mp hcc
          rw [Subgroup.mem_subgroupOf] at h1
          have h2 : (c : G)⁻¹ * (c' : G) ∈ Z ⊓ conjSubgroup r B :=
            ⟨h1, (conjSubgroup r B).mul_mem ((conjSubgroup r B).inv_mem c.2) c'.2⟩
          rw [hinter, Subgroup.mem_bot] at h2
          exact Subtype.ext (inv_mul_eq_one.mp h2)
        calc Nat.card Z = Nat.card (conjSubgroup r B) := hcardB.symm
          _ ≤ _ := Nat.card_le_card_of_injective f hf
      have hmono := relIndex_inf_le_stroth80 (LB M Q (conjSubgroup r B) ⊓ hc.CN t)
        (hc.CN t) (CommQ hQM x) inf_le_right
      have hlt := relIndex_lt_of_card_lt (hc.CN t) (CommQ hQM x) (Nat.card Z) hcount
      exact absurd (le_trans hq (le_trans hcnt hmono)) (not_le.mpr hlt)
    obtain ⟨y, hyP, hyN, hβy⟩ := hexists
    have hconj : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
      step72Split_of h34 hRoot h52a hA G M Q Z B hc n t hs r hr g hgM hgN α hαmem β hβmem
        hβV (c₁ * c₂) hcV hsplit_mem ⟨y, hyP, hyN, hβy⟩
    apply hvn
    exact Subgroup.mem_sup_right (hconj ▸ hv)
  have hZVle : B ⊔ Z ≤ Vt M (LB M Q B) B Z t := sup_le (hc.B_le_Vt ht) sec39_Z_le_Vt
  have hfixed : ∀ v ∈ conjSubgroup g (Vt M (LB M Q B) B Z t), ∀ l ∈ LB M Q B,
      ⁅l, v⁆ ∈ Vt M (LB M Q B) B Z t := by
    intro v hv l hl
    have hv' := hClaimA v hv
    have hv'' : v ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t := by
      rwa [inf_comm] at hv'
    obtain ⟨α, hα, c, hc', hαc⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (H := QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) (K := Vt M (LB M Q B) B Z t)
      (fun w hw => hVnorm w hw.2) hv''
    have hlα : ⁅l, α⁆ ∈ B ⊔ Z := hc.comm_mem_sup_Z_of_mem_LB hl ⟨hα.2.1, hα.1⟩
    have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hl
    have hlc : ⁅l, c⁆ ∈ Vt M (LB M Q B) B Z t := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hlR) c).mp hc'
      rw [commutatorElement_def]
      exact (Vt M (LB M Q B) B Z t).mul_mem h1 ((Vt M (LB M Q B) B Z t).inv_mem hc')
    rw [← hαc, comm_mul_right_expand, hWcent α hα.2 _ hlc]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hZVle hlα) hlc
  exact conjSubgroup_eq_self_iff.mp
    (sec7Q7Fixed_of_inputs hA hPts hCVs G M Q Z B hc n t hs g hgM hgN hfixed)

theorem step72Index_of_normV (hNV : Step72NormVStatement)
    (hC : Sec7ConjStatement) (hC4 : Sec7ConjOm4Statement)
    (hB : Stroth73aOm4BaseStatement) (hZ : Sec7NormZ0Statement) :
    Step72IndexStatement := by
  intro G _ _ M Q Z B hc n t hs hno Z0 hZ0 x hxL hx hxZ
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨g, hgM, hgN, hxg⟩ : ∃ g ∈ M, g ∈ Subgroup.normalizer (LB M Q B : Set G) ∧
      x * (g * t * g⁻¹)⁻¹ ∈ Q := by
    by_cases hom : OmegaMinusNat hc t 2
    · obtain ⟨g, hgM, hgN, hq⟩ := hC4 G M Q Z B hc n t hs hom Z0 hZ0 t htZ0 x hxL hx
      exact ⟨g, hgM, hgN, hq⟩
    · obtain ⟨g, hgM, hgN, hq⟩ := hC G M Q Z B hc n t hs hom Z0 hZ0 t htZ0 x hxL hx
      exact ⟨g, hgM, hgN, hq⟩
  have hV := hNV G M Q Z B hc n t hs hno Z0 hZ0 x hxL hxZ g hgM hgN hxg hlt
  have hgt : g * t * g⁻¹ ∈ Z0 := by
    by_cases hom : OmegaMinusNat hc t 2
    · exact hB G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM hV
    · have hn := hZ G M Q Z B hc n t hs hom Z0 hZ0 g hgM hV
      exact (Subgroup.mem_normalizer_iff.mp hn t).mp htZ0
  apply hxZ
  have hxe : x = (x * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
  rw [hxe]
  exact Z0.mul_mem (hQZ0 hxg) hgt

theorem step72Index_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hZV : Sec7ZVStatement) (hCV : Sec7CVStatement)
    (hC : Sec7ConjStatement) (hC4 : Sec7ConjOm4Statement) (hB : Stroth73aOm4BaseStatement)
    (hZ : Sec7NormZ0Statement) : Step72IndexStatement :=
  step72Index_of_normV
    (step72NormV_of h34 hRoot h52a h52b hA hPts hZV hCV (step72Orbit_of h34 hA hPts)) hC hC4 hB
    hZ

end CFSG.RankThree.GF2n.Stroth80
