module

public import CFSG.Quasithin.Vol2.Ch10SecD211B
public import CFSG.Quasithin.Vol2.Ch10SecDFrattini

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_odd_mem_Xz (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) :
    ∃ x ∈ L, x ∈ Xz T L (v₁ * v₂) ∧ Odd (orderOf x) ∧
      x ∉ Subgroup.centralizer (fsuUL T L I : Set G) := by
  obtain ⟨ht, htn, hv1, hv11, hv2, -⟩ := hd
  obtain ⟨l, hlL, hlo, hlv, hlC⟩ := exists_odd_mem_centralizer h3 hc hv1.1 hv11
  have hlv2 : l * v₂ = v₂ * l :=
    (Subgroup.mem_centralizer_iff.mp (V2_le_centralizer_L h37 h38 h ht htn hv2.1)) l hlL
  have hlz : l ∈ Subgroup.centralizer ({v₁ * v₂} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hlv1 : l * v₁ = v₁ * l := by
      calc l * v₁ = l * v₁ * l⁻¹ * l := by group
        _ = v₁ * l := by rw [hlv]
    calc l * (v₁ * v₂) = v₁ * (l * v₂) := by rw [← mul_assoc, hlv1, mul_assoc]
      _ = v₁ * v₂ * l := by rw [hlv2, mul_assoc]
  exact ⟨l, hlL, mem_oTwoUpper_of_odd ⟨SecA.le_fsuL0 T L hlL, hlz⟩ hlo, hlo, hlC⟩

theorem sq_eq_one_of_mem_Vz (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1029 : Stmt10_2_9) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) :
    ∀ x ∈ Vz v₁ v₂, x ^ 2 = 1 := by
  have hab := (stmt10_2_11_one h37 h38 h1029 h h3 hc hd).1
  have hcomm : ∀ a ∈ Vz v₁ v₂, ∀ b ∈ Vz v₁ v₂, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hab hb).2) a (hab ha).1
  have hE : ∀ e ∈ Subgroup.closure {v₁, v₂}, e ^ 2 = 1 := by
    obtain ⟨ht, -, hv1, -, hv2, -⟩ := hd
    have hV1 : v₁ ∈ fsuVM T L I := V1_le_V hv1.1
    have hV2 : v₂ ∈ fsuVM T L I :=
      commutator_le_left_of_le_normalizer ((SecA.conjugate_le_fsuL0 ht).trans
        (SecA.fsuL0_le_normalizer_fsuVM T L I)) hv2.1
    have hEV : Subgroup.closure {v₁, v₂} ≤ fsuVM T L I := by
      rw [Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact hV1
      · exact hV2
    exact fun e he => (SecA.isElemAbelian_fsuVM h).2 e (hEV he)
  intro x hx
  refine Subgroup.closure_induction (p := fun y hy => y ^ 2 = 1) (fun y hy => ?_) (by simp)
    (fun a b ha hb iha ihb => ?_) (fun a ha iha => ?_) hx
  · obtain ⟨g, -, e, he, rfl⟩ := hy
    have := hE e he
    calc (g * e * g⁻¹) ^ 2 = g * e ^ 2 * g⁻¹ := by
          rw [pow_two, pow_two]; group
      _ = 1 := by rw [this]; group
  · have hab' := hcomm a ha b hb
    calc (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
          rw [pow_two, pow_two, pow_two]
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hab']
            _ = a * a * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  · rw [inv_pow, iha, inv_one]

omit [Finite G] in
theorem mem_centralizer_subgroupOf_iff {V H : Subgroup G} (hVH : V ≤ H) (x : ↥H) :
    x ∈ Subgroup.centralizer ((V.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (x : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx v hv
    have := congrArg Subtype.val (hx ⟨v, hVH hv⟩ (Subgroup.mem_subgroupOf.mpr hv))
    exact this
  · intro hx w hw
    exact Subtype.ext (hx w (Subgroup.mem_subgroupOf.mp hw))

theorem le_normalizer_map_comap {H : Subgroup G} (K : Subgroup ↥H) [K.Normal]
    (P : Subgroup (↥H ⧸ K)) [P.Normal] :
    H ≤ Subgroup.normalizer (((P.comap (QuotientGroup.mk' K)).map H.subtype : Subgroup G) :
      Set G) := by
  intro g hg
  refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨⟨g, hg⟩ * y * (⟨g, hg⟩ : ↥H)⁻¹, ?_, rfl⟩
  show QuotientGroup.mk' K (⟨g, hg⟩ * y * (⟨g, hg⟩ : ↥H)⁻¹) ∈ P
  rw [map_mul, map_mul, map_inv]
  exact ‹P.Normal›.conj_mem _ hy _

omit [Finite G] in
theorem T1_le_centralizer_E {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) :
    T1 T L ≤ Subgroup.centralizer ((Subgroup.closure {v₁, v₂} : Subgroup G) : Set G) := by
  obtain ⟨-, -, hv1, -, hv2, -⟩ := hd
  rw [Subgroup.centralizer_closure]
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  rintro w (rfl | rfl)
  · exact ((Subgroup.mem_centralizer_iff.mp hv1.2) s hs).symm
  · exact ((Subgroup.mem_centralizer_iff.mp hv2.2) s hs).symm

theorem le_centralizer_Vz_of_le_T1 {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂)
    {Pt : Subgroup G} (hRs : IsSylowTwoOf (T ⊓ Pt) Pt)
    (hPtGz : Pt ≤ Subgroup.centralizer ({v₁ * v₂} : Set G))
    (hGzPt : Subgroup.centralizer ({v₁ * v₂} : Set G) ≤ Subgroup.normalizer (Pt : Set G))
    (hcov : ∀ p ∈ Pt, ∃ c ∈ Subgroup.centralizer ({v₁ * v₂} : Set G) ⊓
      Subgroup.centralizer (Vz v₁ v₂ : Set G), ∃ r ∈ T ⊓ Pt, p = c * r)
    (hR1 : T ⊓ Pt ≤ T1 T L) : T ⊓ Pt ≤ Subgroup.centralizer (Vz v₁ v₂ : Set G) := by
  intro r hr
  rw [Vz, conjClosure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro _ ⟨g, hg, e, he, rfl⟩
  obtain ⟨c, hc, m, hm, rfl⟩ := exists_mul_normalizer_of_cover hRs hPtGz hGzPt hcov hg
  have hr' : m⁻¹ * r * m⁻¹⁻¹ ∈ T ⊓ Pt :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hm.2) r).mp hr
  have hre : (m⁻¹ * r * m) * e = e * (m⁻¹ * r * m) := by
    have h1 := T1_le_centralizer_E hd (hR1 (by simpa using hr'))
    exact ((Subgroup.mem_centralizer_iff.mp h1) e he).symm
  have hmeVz : m * e * m⁻¹ ∈ Vz v₁ v₂ := mem_conjClosure hm.1 he
  have hcVz := (Subgroup.mem_centralizer_iff.mp hc.2) _ hmeVz
  have hconj : c * m * e * (c * m)⁻¹ = m * e * m⁻¹ := by
    calc c * m * e * (c * m)⁻¹ = c * (m * e * m⁻¹) * c⁻¹ := by group
      _ = (m * e * m⁻¹) * c * c⁻¹ := by rw [← hcVz]
      _ = m * e * m⁻¹ := by group
  rw [hconj]
  calc m * e * m⁻¹ * r = m * (e * (m⁻¹ * r * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * r * m) * e) * m⁻¹ := by rw [hre]
    _ = r * (m * e * m⁻¹) := by group

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← SecA.conjugate_eq_self_iff] at hA hB ⊢
  rw [CFSG.conjugate, Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) hA hB

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hA y,
    Subgroup.mem_normalizer_iff.mp hB y]

end CFSG.Quasithin.Vol2.Ch10.SecD
