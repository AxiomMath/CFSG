module

public import CFSG.Monster.GMS.ASegTitsSub
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3024
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10042
public import Certificates.Certificate10043
public import Certificates.Certificate10044
public import Certificates.Certificate10045
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate10072
public import Certificates.Certificate10073
public import Certificates.Certificate10074
public import Certificates.Certificate10075
public import Certificates.Certificate10076
public import Certificates.Certificate8955

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog CFSG.Monster.GMS.S4Assembly
  CFSG.Monster.GMS.S4Family

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Arcs

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

omit [Finite G] in
theorem mul_comm_of_isConj_a (hG : GMSF1Type d₀ a z₀) {p q : G} (hp : IsConj a p)
    (hq : IsConj a q) (hpq : IsConj a (p * q)) : p * q = q * p :=
  mul_comm_of_mul_self_eq_one (S365.sq_of_isConj_a hG.1.1 hp) (S365.sq_of_isConj_a hG.1.1 hq)
    (S365.sq_of_isConj_a hG.1.1 hpq)

theorem harc_twoAGraph
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    ∀ p q p' q' : ConjVert a, (twoAGraph a).Adj p q → (twoAGraph a).Adj p' q' →
      ∃ g : G, g • p = p' ∧ g • q = q' := by
  intro p q p' q' hpq hpq'
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 (p.2.symm.trans p'.2)
  have hq₁ : g₁ * (q : G) * g₁⁻¹ ∈ twoANbr a (p' : G) := by
    refine ⟨isConj_conj q.2 g₁, ?_⟩
    have := isConj_conj hpq.2 g₁
    rwa [conj_mul_conj, hg₁] at this
  obtain ⟨h, hh, hhq⟩ := table7_transitive I.sls I.tableV I.leech I.tableIII I.tableIVBaby
    I.threeSwap I.leechPair hG p'.2 (K := .two_A) hq₁ (show (q' : G) ∈ twoANbr a (p' : G) from
      ⟨q'.2, hpq'.2⟩)
  refine ⟨h * g₁, Subtype.ext ?_, Subtype.ext ?_⟩
  · show h * g₁ * (p : G) * (h * g₁)⁻¹ = p'
    rw [show h * g₁ * (p : G) * (h * g₁)⁻¹ = h * (g₁ * p * g₁⁻¹) * h⁻¹ by group, hg₁]
    exact conj_eq_of_mem_centralizer hh
  · show h * g₁ * (q : G) * (h * g₁)⁻¹ = q'
    rw [show h * g₁ * (q : G) * (h * g₁)⁻¹ = h * (g₁ * q * g₁⁻¹) * h⁻¹ by group]
    exact hhq

end Arcs

section Triangles

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ y z : G}

theorem ASegData.exists_fixing_of_ne (EL : EightGroupLines a z₀) (hG : GMSF1Type d₀ a z₀)
    (D : ASegData a z₀ y z) {c : G} (hc : IsConj a c) (hac : IsConj a (a * c))
    (hyc : IsConj a (y * c)) (hca : c ≠ a) (hcy : c ≠ y) (hcay : c ≠ a * y) :
    ∃ g : G, g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y ∧ g * (a * y * z) * g⁻¹ = c := by
  have h := D.comm3 hG
  have hn : ∀ {w : G}, IsConj a w → ¬ IsConj z₀ w := fun hw hB => not_isConj_of_isConj hG hw hB
  have hc2 : c * c = 1 := S365.sq_of_isConj_a hG.1.1 hc
  have hac' : a * c = c * a := mul_comm_of_isConj_a hG (IsConj.refl a) hc hac
  have hyc' : y * c = c * y := mul_comm_of_isConj_a hG D.isConj_y hc hyc
  have hc3 : Comm3 a y c := ⟨h.aa, h.yy, hc2, h.ay, hac', hyc'⟩
  have hl : IsLineTriple a a y := ⟨IsConj.refl a, D.isConj_y, D.isConj_ay⟩
  have hz2 : orderOf z = 2 := orderOf_eq_two_of_isConj_z₀ hG D.isConj_z
  have hez : IsEightExt a y z := ⟨h.zz, h.za, h.zy, ne_one_of_orderOf hz2,
    fun e => hn (IsConj.refl a) (e ▸ D.isConj_z), fun e => hn D.isConj_y (e ▸ D.isConj_z),
    fun e => hn D.isConj_ay (e ▸ D.isConj_z)⟩
  have hec : IsEightExt a y c := ⟨hc2, hac'.symm, hyc'.symm, S365.ne_one_of_isConj_a hG.1.1 hc,
    hca, hcy, hcay⟩
  have hna : ¬ IsConj z₀ (c * a) := hn (by rw [← hac']; exact hac)
  have hny : ¬ IsConj z₀ (c * y) := hn (by rw [← hyc']; exact hyc)
  have hcz : twoBCount z₀ a y z = 1 := by
    rw [S365.twoBCount_eq_ite]
    have h1 : ¬ IsConj z₀ (z * a) := hn (by rw [h.za]; exact D.isConj_az)
    have h2 : ¬ IsConj z₀ (z * y) := hn (by rw [h.zy]; exact D.isConj_yz)
    have h3 : ¬ IsConj z₀ (z * a * y) :=
      hn (by rw [show z * a * y = a * y * z by comm3_simp h]; exact D.isConj_ayz)
    simp [D.isConj_z, h1, h2, h3, -isConj_iff]
  have hcc : twoBCount z₀ a y c = 1 := by
    have hle : twoBCount z₀ a y c ≤ 1 := by
      rw [S365.twoBCount_eq_ite]
      simp only [hn hc, hna, hny, ite_false]
      split_ifs <;> omega
    rcases EL.1 a y c hl hec with e | e | e <;> omega
  obtain ⟨g, hga, hgy, hgz⟩ := EL.2 a y z a y c hl hez hl hec (hcz.trans hcc.symm)
  have hB : IsConj z₀ (g * z * g⁻¹) := D.isConj_z.trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hz' : g * z * g⁻¹ = c * a * y := by
    rcases hgz with e | e | e | e
    · exact absurd hB (by rw [e]; exact hn hc)
    · exact absurd hB (by rw [e]; exact hna)
    · exact absurd hB (by rw [e]; exact hny)
    · exact e
  refine ⟨g, hga, hgy, ?_⟩
  rw [show g * (a * y * z) * g⁻¹ = (g * a * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹) by group, hga,
    hgy, hz']
  comm3_simp hc3


theorem ASegData.exists_triangle
    (I : GMSInterfaces d₀ G) (EL : EightGroupLines a z₀)
    (hG : GMSF1Type d₀ a z₀) (D : ASegData a z₀ y z) {y₁ y₂ : G} (hy₁ : IsConj a y₁)
    (hy₂ : IsConj a y₂) (ha1 : IsConj a (a * y₁)) (h12 : IsConj a (y₁ * y₂)) (hne12 : y₁ ≠ y₂)
    (h2a : IsConj a (y₂ * a)) (hne2a : y₂ ≠ a) :
    (∃ g ∈ C[a], g * y * g⁻¹ = y₁ ∧ g * (a * y) * g⁻¹ = y₂) ∨
      (∃ g ∈ C[a], g * y * g⁻¹ = y₁ ∧ g * (a * y * z) * g⁻¹ = y₂) := by
  obtain ⟨h₁, hh₁, hhy⟩ := table7_transitive I.sls I.tableV I.leech I.tableIII I.tableIVBaby
    I.threeSwap I.leechPair hG (IsConj.refl a) (K := .two_A)
    (show y ∈ twoANbr a a from ⟨D.isConj_y, D.isConj_ay⟩)
    (show y₁ ∈ twoANbr a a from ⟨hy₁, ha1⟩)
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = h₁⁻¹ * y₂ * h₁ := ⟨_, rfl⟩
  have hy₂c : h₁ * c * h₁⁻¹ = y₂ := by rw [hcdef]; group
  have hc : IsConj a c := by
    have := isConj_conj hy₂ h₁⁻¹
    rwa [inv_inv, ← hcdef] at this
  have hcomm : h₁⁻¹ * a = a * h₁⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.1 ((C[a]).inv_mem hh₁)
  have ha2 : IsConj a (a * y₂) := by
    have := isConj_conj h2a a
    rwa [show a * (y₂ * a) * a⁻¹ = a * y₂ by group] at this
  have hac : IsConj a (a * c) := by
    have e : a * c = h₁⁻¹ * (a * y₂) * h₁ := by
      rw [hcdef]
      calc a * (h₁⁻¹ * y₂ * h₁) = (a * h₁⁻¹) * y₂ * h₁ := by group
        _ = (h₁⁻¹ * a) * y₂ * h₁ := by rw [hcomm]
        _ = h₁⁻¹ * (a * y₂) * h₁ := by group
    rw [e, isConj_conj_inv_iff]
    exact ha2
  have hyc : IsConj a (y * c) := by
    have e : y * c = h₁⁻¹ * (y₁ * y₂) * h₁ := by rw [← hhy, hcdef]; group
    rw [e, isConj_conj_inv_iff]
    exact h12
  have hca : c ≠ a := fun e =>
    hne2a (by rw [← hy₂c, e]; exact conj_eq_of_mem_centralizer hh₁)
  have hcy : c ≠ y := fun e => hne12 (by rw [← hy₂c, e, hhy])
  by_cases hcay : c = a * y
  · exact Or.inl ⟨h₁, hh₁, hhy, by rw [← hcay]; exact hy₂c⟩
  · obtain ⟨g, hga, hgy, hgc⟩ := D.exists_fixing_of_ne EL hG hc hac hyc hca hcy hcay
    refine Or.inr ⟨h₁ * g, Subgroup.mul_mem _ hh₁ (mem_centralizer_of_conj_eq hga), ?_, ?_⟩
    · rw [show h₁ * g * y * (h₁ * g)⁻¹ = h₁ * (g * y * g⁻¹) * h₁⁻¹ by group, hgy, hhy]
    · rw [show h₁ * g * (a * y * z) * (h₁ * g)⁻¹ = h₁ * (g * (a * y * z) * g⁻¹) * h₁⁻¹ by group,
        hgc, hy₂c]

end Triangles

section Vertices

variable {G : Type} [Group G] {z₀ a y z : G}

@[expose] def vertA (a : G) : ConjVert a := ⟨a, IsConj.refl a⟩

@[expose] def vertY (D : ASegData a z₀ y z) : ConjVert a := ⟨y, D.isConj_y⟩

@[expose] def vertU (D : ASegData a z₀ y z) : Bool → ConjVert a
  | false => ⟨a * y, D.isConj_ay⟩
  | true => ⟨a * y * z, D.isConj_ayz⟩

@[expose] def XtB (a y z : G) : Bool → Subgroup G
  | false => Xt0 a y
  | true => Xt1 a y z

theorem smul_mk_eq_mk_iff {x x' : G} (hx : IsConj a x) (hx' : IsConj a x') (g : G) :
    g • (⟨x, hx⟩ : ConjVert a) = ⟨x', hx'⟩ ↔ g * x * g⁻¹ = x' := Subtype.ext_iff

theorem mem_edgeStab_iff (D : ASegData a z₀ y z) {g : G} :
    g ∈ edgeStab (vertA a) (vertY D) ↔
      (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨ (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a) := by
  rw [mem_edgeStab]
  exact or_congr (and_congr (smul_mk_eq_mk_iff _ _ g) (smul_mk_eq_mk_iff _ _ g))
    (and_congr (smul_mk_eq_mk_iff _ _ g) (smul_mk_eq_mk_iff _ _ g))

end Vertices

section TitsHypotheses

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ y z : G}

omit [Finite G] in
theorem aseg_adj (hG : GMSF1Type d₀ a z₀) (D : ASegData a z₀ y z) :
    (twoAGraph a).Adj (vertA a) (vertY D) :=
  ⟨fun e => D.a_ne_y hG (congrArg Subtype.val e), D.isConj_ay⟩

omit [Finite G] in
theorem aseg_hXt (D : ASegData a z₀ y z) (j : Bool) {g : G} (hg : g ∈ XtB a y z j) :
    g • vertA a = vertA a ∨ g • vertA a = vertY D ∨ g • vertA a = vertU D j := by
  cases j
  · have h : g * a * g⁻¹ ∈ tri0 a y := (Subgroup.mem_set_normalizer_iff.1 hg a).1 (Or.inl rfl)
    rcases h with e | e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Or.inl (Subtype.ext e))
    · exact Or.inr (Or.inr (Subtype.ext e))
  · have h : g * a * g⁻¹ ∈ tri1 a y z :=
      (Subgroup.mem_set_normalizer_iff.1 hg.2 a).1 (Or.inl rfl)
    rcases h with e | e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Or.inl (Subtype.ext e))
    · exact Or.inr (Or.inr (Subtype.ext e))

theorem aseg_hτ (EL : EightGroupLines a z₀) (hG : GMSF1Type d₀ a z₀) (D : ASegData a z₀ y z)
    (j : Bool) : ∃ g ∈ XtB a y z j, g • vertA a = vertY D ∧ g • vertY D = vertA a := by
  have h := D.comm3 hG
  obtain ⟨s, hs1, hs2, hs3⟩ := D.exists_s EL hG
  cases j
  · exact ⟨s, mem_Xt0_of_fix_or_swap h (Or.inr ⟨hs1, hs2⟩), Subtype.ext hs1, Subtype.ext hs2⟩
  · exact ⟨s, mem_Xt1_of_swap h hs1 hs2 hs3, Subtype.ext hs1, Subtype.ext hs2⟩

theorem aseg_hρ (EL : EightGroupLines a z₀) (hG : GMSF1Type d₀ a z₀) (D : ASegData a z₀ y z)
    (j : Bool) : ∃ g ∈ XtB a y z j, g • vertA a = vertY D ∧ g • vertY D = vertU D j ∧
      g • vertU D j = vertA a := by
  have h := D.comm3 hG
  cases j
  · obtain ⟨r, hr1, hr2, hr3⟩ := D.exists_r₀ EL hG
    refine ⟨r, mem_Xt0_of_cycle h hr1 hr2, Subtype.ext hr1, Subtype.ext hr2, Subtype.ext ?_⟩
    show r * (a * y) * r⁻¹ = a
    rw [conj_mul_conj, hr1, hr2, show y * (a * y) = a by comm3_simp h]
  · obtain ⟨r, hr1, hr2, hr3⟩ := D.exists_r₁ EL hG
    refine ⟨r, mem_Xt1_of_cycle h hr1 hr2 hr3, Subtype.ext hr1, Subtype.ext hr2, Subtype.ext ?_⟩
    show r * (a * y * z) * r⁻¹ = a
    rw [show r * (a * y * z) * r⁻¹ = (r * a * r⁻¹) * (r * y * r⁻¹) * (r * z * r⁻¹) by group, hr1,
      hr2, hr3, show y * (a * y * z) * z = a by comm3_simp h]

theorem aseg_htri
    (I : GMSInterfaces d₀ G) (EL : EightGroupLines a z₀) (hG : GMSF1Type d₀ a z₀)
    (D : ASegData a z₀ y z) :
    ∀ y₁ y₂ : ConjVert a, (twoAGraph a).Adj (vertA a) y₁ → (twoAGraph a).Adj y₁ y₂ →
      (twoAGraph a).Adj y₂ (vertA a) →
        ∃ j : Bool, ∃ g : G, g • vertA a = vertA a ∧ g • vertY D = y₁ ∧ g • vertU D j = y₂ := by
  intro y₁ y₂ h1 h12 h2
  rcases D.exists_triangle I EL hG y₁.2 y₂.2 h1.2 h12.2 (fun e => h12.1 (Subtype.ext e)) h2.2
    (fun e => h2.1 (Subtype.ext e)) with ⟨g, hg, e1, e2⟩ | ⟨g, hg, e1, e2⟩
  · exact ⟨false, g, Subtype.ext (conj_eq_of_mem_centralizer hg), Subtype.ext e1,
      Subtype.ext e2⟩
  · exact ⟨true, g, Subtype.ext (conj_eq_of_mem_centralizer hg), Subtype.ext e1,
      Subtype.ext e2⟩

@[expose] def asegTitsData
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (D : ASegData a z₀ y z) (hconn : (twoAGraph a).Preconnected)
    (hΓ : Triangulable (twoAGraph a)) : TitsData (twoAGraph a) G Bool :=
  titsData_twoAGraph (vertA a) (vertY D) (aseg_adj hG D) hconn hΓ (harc_twoAGraph I hG) (vertU D)
    (XtB a y z) (aseg_hXt D) (aseg_hτ (eightGroupLines_of I hG) hG D)
    (aseg_hρ (eightGroupLines_of I hG) hG D) (aseg_htri I (eightGroupLines_of I hG) hG D)

end TitsHypotheses

end CFSG.Monster.GMS
