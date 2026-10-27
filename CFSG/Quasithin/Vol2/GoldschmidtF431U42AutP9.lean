module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP9Fus
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP9Dih
public import CFSG.Dihedral.DisconnectedInvolutionGraph.TwoInvolutions
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6All
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Cj

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)
open CFSG.DisconnectedInvolutionGraph.Helpers (Involution)

variable {G : Type} [Group G] [Finite G]

theorem isConj_of_cen_le {K : Subgroup G} (hcen : ∀ i ∈ K, i ^ 2 = 1 → i ≠ 1 → cenOf i ≤ K)
    {a c₀ : G} (ha : a ∈ K) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) (hc : c₀ ∉ K) (hc2 : c₀ ^ 2 = 1)
    (hc1 : c₀ ≠ 1) : IsConj a c₀ := by
  have hoa : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hoc : orderOf c₀ = 2 := orderOf_eq_prime hc2 hc1
  rcases Nat.even_or_odd (orderOf (a * c₀)) with heven | hodd
  · exfalso
    obtain ⟨d, had, hcd⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.even_product_common_involution
      (⟨a, hoa⟩ : Involution G) ⟨c₀, hoc⟩ heven
    have hd2 : (d : G) ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, d.property]
    have hd1 : (d : G) ≠ 1 := by
      intro h
      have := d.property
      rw [h, orderOf_one] at this
      omega
    have hdK : (d : G) ∈ K := by
      refine hcen a ha ha2 ha1 ?_
      rw [cenOf, Subgroup.mem_centralizer_singleton_iff]
      exact had.symm
    refine hc (hcen d hdK hd2 hd1 ?_)
    rw [cenOf, Subgroup.mem_centralizer_singleton_iff]
    exact hcd
  · obtain ⟨e, he⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.odd_product_conjugates
      (⟨a, hoa⟩ : Involution G) ⟨c₀, hoc⟩ hodd
    refine isConj_iff.2 ⟨(a * c₀) ^ e, ?_⟩
    have h := congrArg Subtype.val he
    simp only [CFSG.DisconnectedInvolutionGraph.Helpers.conjugateInvolution] at h
    rwa [MulAut.conj_apply] at h

omit [Finite G] in
theorem cen_le_of_conj {K : Subgroup G} {i u m : G} (hm : m ∈ K) (h : m * i * m⁻¹ = u)
    (hu : cenOf u ≤ K) : cenOf i ≤ K := by
  intro g hg
  have hg' : m * g * m⁻¹ ∈ cenOf u := by
    rw [cenOf, Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    rw [← h]
    calc m * g * m⁻¹ * (m * i * m⁻¹) = m * (g * i) * m⁻¹ := by group
      _ = m * (i * g) * m⁻¹ := by rw [hg]
      _ = m * i * m⁻¹ * (m * g * m⁻¹) := by group
  have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) (hu hg')) hm
  simpa [mul_assoc] using this

section Norm

variable {M₁ M₂ : Subgroup G} {z : G}

theorem u42AutF56_norm (c : AutCtx G M₁ M₂ z) (h2 : U42AutSylow) (h5 : U42AutFusionZ)
    (hfz : IsConj (c.iso.toG fhB * z) z) (ht0 : IsConj (c.iso.toG t0B) (c.iso.toG fhB))
    {R : Subgroup G} (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB)))
    (hTR : c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≤ R) (hR64 : Nat.card ↥R = 2 ^ 6)
    (hD : Nonempty (↥R ≃* DihedralGroup 4 × DihedralGroup 4))
    (hcF : Nat.card ↥(cenOf (c.iso.toG fhB)) = 2880)
    (hcF0 : Nat.card ↥((M₁ ⊔ M₂) ⊓ cenOf (c.iso.toG fhB)) = 1440) :
    (M₁ ⊔ M₂) ⊔ Subgroup.normalizer (aOf M₂ (c.iso.toG fhB) : Set G) = ⊤ := by
  rw [show aOf M₂ (c.iso.toG fhB) = c.iso.imgG A2h from aOf_M2 c.iso]
  by_contra hK
  set F := c.iso.toG fhB with hF
  set T₀ := c.iso.imgG That with hT₀
  set N := Subgroup.normalizer (c.iso.imgG A2h : Set G) with hN
  set K := (M₁ ⊔ M₂) ⊔ N with hKdef
  have hZ : ZStmt c := zStmt c h5 hfz ht0
  have hT₀G : IsSylowTwoOf T₀ ⊤ := h2 G M₁ M₂ z c _ (isSylowTwoOf_imgG_That c.iso)
  have hT₀M : T₀ ≤ M₁ ⊓ M₂ := (isSylowTwoOf_imgG_That c.iso).1
  have hM₀K : M₁ ⊔ M₂ ≤ K := le_sup_left
  have hNK : N ≤ K := le_sup_right
  have hT₀K : T₀ ≤ K := hT₀M.trans (inf_le_left.trans (le_sup_left.trans hM₀K))
  have hodd : ¬ 2 ∣ T₀.index := by
    have e : (T₀.subgroupOf ⊤).index = T₀.index := Subgroup.relIndex_top_right _
    have := hT₀G.2.2
    rwa [e] at this
  have hSylK : IsSylowTwoOf T₀ K := by
    refine ⟨hT₀K, hT₀G.2.1, fun hd => hodd ?_⟩
    rw [← Subgroup.relIndex_mul_index hT₀K]
    exact Dvd.dvd.mul_right hd _
  have hconj : ∀ {i : G}, i ∈ K → i ^ 2 = 1 → i ≠ 1 →
      (∃ m ∈ K, m * i * m⁻¹ = z) ∨ (∃ m ∈ K, m * i * m⁻¹ = F) := by
    intro i hi hi2 hi1
    have hp : IsPGroup 2 (Subgroup.zpowers i) :=
      isPGroup_zpowers_of_sq (by rw [← pow_two]; exact hi2)
    obtain ⟨x, hx, hxS⟩ := F7.isSylowTwoOf_exists_conj_le hSylK (Subgroup.zpowers_le.2 hi) hp
    have hiT : x⁻¹ * i * x ∈ T₀ := mem_conjSub.1 (hxS (Subgroup.mem_zpowers i))
    obtain ⟨û, hûT, hû⟩ := c.iso.mem_imgG.1 hiT
    have hû2 : û * û = 1 := by
      apply c.iso.toG_injective
      rw [AutIso.toG_mul, hû, c.iso.toG_one]
      calc x⁻¹ * i * x * (x⁻¹ * i * x) = x⁻¹ * i ^ 2 * x := by rw [pow_two]; group
        _ = 1 := by rw [hi2]; group
    have hû1 : (û : Ah) ≠ 1 := by
      intro h1
      apply hi1
      have h2' := congrArg c.iso.toG (Subtype.ext h1 : û = 1)
      rw [hû, c.iso.toG_one] at h2'
      calc i = x * (x⁻¹ * i * x) * x⁻¹ := by group
        _ = 1 := by rw [h2']; group
    have hconjK : ∀ {w : G} {m : G}, m ∈ K → m * (x⁻¹ * i * x) * m⁻¹ = w →
        ∃ m' ∈ K, m' * i * m'⁻¹ = w := by
      intro w m hm h
      refine ⟨m * x⁻¹, Subgroup.mul_mem _ hm (Subgroup.inv_mem _ hx), ?_⟩
      rw [← h]
      group
    rcases inv_conj_K c hZ hT₀G hûT hû2 hû1 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · rw [hû] at h
      exact Or.inl (hconjK hm h)
    · rw [hû] at h
      exact Or.inr (hconjK hm h)
  have hcz : cenOf z ≤ K := by
    rw [c.cenOf_z]
    exact le_sup_left.trans hM₀K
  have hAR : c.iso.imgG A2h ≤ R := by
    intro a ha
    have haT : a ∈ T₀ := imgG_mono' c.iso A2h_le_That ha
    have hab := imgG_E16 c.iso (K := A2h) (fun a ha b hb => A2h_comm ha hb) fun a ha => A2h_sq ha
    have hFA : F ∈ c.iso.imgG A2h :=
      c.iso.mem_imgG.2 ⟨fhB, ⟨fhatL, A_cent_check.2.2.2.2.2.1, repL_fhat⟩, rfl⟩
    have haF : a ∈ cenOf F := by
      rw [cenOf, Subgroup.mem_centralizer_singleton_iff]
      exact (hab.1 F hFA a ha).symm
    exact hTR ⟨haT, haF⟩
  have hab := imgG_E16 c.iso (K := A2h) (fun a ha b hb => A2h_comm ha hb) fun a ha => A2h_sq ha
  have hA16 : Nat.card ↥(c.iso.imgG A2h) = 16 := by
    rw [c.iso.card_imgG (A2h_le_That.trans That_le_Bh), card_A2h]
  have hRN : R ≤ N := le_normalizer_of_dihedral hD hAR hA16 hab.2
  have hcF' : cenOf F ≤ K := by
    set C₀ : Subgroup G := (M₁ ⊔ M₂) ⊓ cenOf F with hC₀
    have hRnot : ¬ R ≤ C₀ := by
      intro h
      have := Subgroup.card_dvd_of_le h
      rw [hR64, hcF0] at this
      norm_num at this
    obtain ⟨r, hrR, hrC⟩ : ∃ r ∈ R, r ∉ C₀ := by
      by_contra hcon
      push Not at hcon
      exact hRnot hcon
    set D : Subgroup G := C₀ ⊔ Subgroup.zpowers r with hD'
    have hDc : D ≤ cenOf F := sup_le inf_le_right (Subgroup.zpowers_le.2 (hR.1 hrR))
    have hDK : D ≤ K :=
      sup_le (inf_le_left.trans hM₀K) (Subgroup.zpowers_le.2 (hNK (hRN hrR)))
    have hC₀D : C₀ ≤ D := le_sup_left
    have hrD : r ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hC₀D
    have hD2 : Nat.card D ≤ 2880 :=
      Nat.le_of_dvd (by norm_num) (hcF ▸ Subgroup.card_dvd_of_le hDc)
    have hDpos : 0 < Nat.card D := Nat.card_pos
    rw [hcF0] at hk
    have hk2 : k = 1 ∨ k = 2 := by omega
    rcases hk2 with rfl | rfl
    · exfalso
      have := Subgroup.eq_of_le_of_card_ge hC₀D (by omega)
      exact hrC (this ▸ hrD)
    · have := Subgroup.eq_of_le_of_card_ge hDc (by omega)
      exact this ▸ hDK
  have hcenK : ∀ i ∈ K, i ^ 2 = 1 → i ≠ 1 → cenOf i ≤ K := by
    intro i hi hi2 hi1
    rcases hconj hi hi2 hi1 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · exact cen_le_of_conj hm h hcz
    · exact cen_le_of_conj hm h hcF'
  have hex : ∃ c₀ : G, c₀ ∉ K ∧ c₀ ^ 2 = 1 ∧ c₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hK
    refine eq_top_iff.2 fun g _ => ?_
    have hw2 : (g * z * g⁻¹) ^ 2 = 1 := by
      calc (g * z * g⁻¹) ^ 2 = g * z ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [c.z2]; group
    have hw1 : g * z * g⁻¹ ≠ 1 := by
      intro h1
      apply c.z1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have hwK : g * z * g⁻¹ ∈ K := by
      by_contra hw
      exact hw1 (hcon _ hw hw2)
    rcases hconj hwK hw2 hw1 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · have hmg : m * g ∈ cenOf z := by
        rw [cenOf, Subgroup.mem_centralizer_singleton_iff]
        calc m * g * z = (m * (g * z * g⁻¹) * m⁻¹) * (m * g) := by group
          _ = z * (m * g) := by rw [h]
      have hg : g = m⁻¹ * (m * g) := by group
      rw [hg]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) (hcz hmg)
    · exfalso
      apply F_notConj c h5
      exact (isConj_iff.2 ⟨m * g, by rw [← hF, ← h]; group⟩).symm
  obtain ⟨c₀, hc₀K, hc₀2, hc₀1⟩ := hex
  have hzM : z ∈ M₁ := by
    rw [← c.cenOf_z]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzK : z ∈ K := hM₀K (Subgroup.mem_sup_left hzM)
  have hFK : F ∈ K := hM₀K (Subgroup.mem_sup_left (c.iso.toG_mem fhB).1)
  have hF2 : F ^ 2 = 1 := by
    rw [pow_two]
    exact F_sq c.iso
  have h1 := isConj_of_cen_le hcenK hzK c.z2 c.z1 hc₀K hc₀2 hc₀1
  have h2' := isConj_of_cen_le hcenK hFK hF2 (F_ne_one c.iso) hc₀K hc₀2 hc₀1
  exact F_notConj c h5 (h2'.trans h1.symm)

theorem u42AutF56 : U42AutF56 := by
  intro G _ _ M₁ M₂ z c T hT f hfT hf R hR hTR hC h54 h55
  obtain ⟨hcF, hcF0, -⟩ := h55
  obtain ⟨g, hgB, -, hTg, hfg⟩ := exists_norm c hT hfT hf
  have hF : (c.conj hgB).iso.toG fhB = f := by
    rw [hfg]
    exact AutIso.toG_conjIso c.iso hgB fhB
  have hT' : (c.conj hgB).iso.imgG That = T := by
    rw [hTg]
    exact AutIso.imgG_conjIso c.iso hgB That
  have h2 : U42AutSylow := u42AutSylow
  have h5 : U42AutFusionZ := u42AutFusionZ
  obtain ⟨hR64, -, hfz, ⟨t, htT, ht2, htcard, htF⟩, -⟩ := hC
  rw [← hF] at hR hTR hcF hcF0 hfz htF h54 ⊢
  rw [← hT'] at hTR htT htcard
  obtain ⟨c0, hc0⟩ := isConj_iff.1 htF
  have ht : c0⁻¹ * (c.conj hgB).iso.toG fhB * c0 = t := by rw [← hc0]; group
  have ht0 : IsConj ((c.conj hgB).iso.toG t0B) ((c.conj hgB).iso.toG fhB) :=
    t0_conj_F (c.conj hgB) h5 (g := c0) (by rw [ht]; exact htT) (by rw [ht]; exact ht2)
      (by rw [ht]; exact htcard)
  exact u42AutF56_norm (c.conj hgB) h2 h5 hfz ht0 hR hTR hR64 h54.2.2.2.2.1 hcF hcF0

end Norm

end CFSG.Quasithin.H13.F431.U42Aut
