module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadM2Fam
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Red

public section

namespace CFSG.Quasithin.J4Fam

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Quasithin.F134.J4E9
  CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Rad

noncomputable abbrev M3 : Subgroup J := Subgroup.normalizer (V0 : Set J)

@[expose] noncomputable def X5 : Set (J ⧸ Hj) := {w | ∃ m ∈ M3, m • basePt = w}

@[expose] noncomputable def D5 : Set (J ⧸ Hj) :=
  {w | ∃ d ∈ Subgroup.centralizer (V0 : Set J), d • basePt = w}

theorem D_le_M3 : Subgroup.centralizer (V0 : Set J) ≤ M3 :=
  Subgroup.centralizer_le_normalizer _

section Str


theorem Eg_le_D (hM : MatFacts) : Eg uJ 11 ≤ Subgroup.centralizer (V0 : Set J) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Eg_comm (elem_uJ hM) (V0_le_Eg' hM hv) hx

theorem X5_subset : X5 ⊆ insert basePt BV := by
  have hM := j4Facts.mat
  rintro _ ⟨n, hn, rfl⟩
  by_cases hnH : n ∈ Hj
  · exact Or.inl (smul_basePt_eq_self_iff.mpr hnH)
  · right
    refine ⟨?_, n, (smul_basePt_eq_mk n).symm, ?_⟩
    · rw [smul_basePt_eq_mk]
      intro h
      exact hnH (mk_eq_basePt_iff.mp h)
    · intro x hx
      have h1 := inv_conj_mem_of_mem_normalizer hn hx
      exact V0_le_Eg' hM h1

theorem exists_mem_normalizer_not_mem_Hj (hF : J4Facts) : ∃ n ∈ M3, n ∉ Hj := by
  have hM := hF.mat
  obtain ⟨g, hgH, hg⟩ := exists_BV hM
  have hg' : g⁻¹ ∉ Hj := fun h => hgH (by simpa using Hj.inv_mem h)
  have hsub : ((conjSub g⁻¹ V0 : Subgroup J) : Set J) ⊆ Ig g⁻¹ := by
    intro x hx
    have hv : (g⁻¹)⁻¹ * x * g⁻¹ ∈ V0 := mem_conjSub.mp hx
    have hxE : x ∈ Eg uJ 11 := by
      have h1 := hg _ hv
      have e : g⁻¹ * ((g⁻¹)⁻¹ * x * g⁻¹) * g = x := by group
      rwa [e] at h1
    exact ⟨hxE, V0_le_Eg' hM hv⟩
  have hc8 : (Ig g⁻¹).ncard ≤ 8 := card_inter_le hF hg'
  have hn : ((conjSub g⁻¹ V0 : Subgroup J) : Set J).ncard = 8 := by
    rw [ncard_conjSub, ← Nat.card_coe_set_eq]
    exact card_V0 hM
  have heq : ((conjSub g⁻¹ V0 : Subgroup J) : Set J) = Ig g⁻¹ :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hn]; exact hc8) (Set.toFinite _)
  rcases inter_trio hF hg' with h2 | ⟨W, hW, hWc⟩
  · exfalso
    rw [← heq, hn] at h2
    omega
  · have hWsub : maskSub W = conjSub g⁻¹ V0 := by
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc, rfl⟩ := (mem_maskSub_iff hM (trio_xor W hW).1 (trio_xor W hW).2).1 hx
        have hclt : c < 2048 := (trio_prop.2 W hW).2.1 c hc
        have h3 : eta uJ 11 c ∈ Ig g⁻¹ := (hWc c hclt).2 hc
        rw [← heq] at h3
        exact h3
      · intro hx
        have hxI : x ∈ Ig g⁻¹ := by
          rw [← heq]
          exact hx
        obtain ⟨c, hclt, hxc⟩ := (mem_Eg_iff (elem_uJ hM)).1 hxI.1
        have h3 : eta uJ 11 c ∈ Ig g⁻¹ := hxc ▸ hxI
        have hcW : c ∈ W := (hWc c hclt).1 h3
        rw [hxc]
        exact (mem_maskSub_iff hM (trio_xor W hW).1 (trio_xor W hW).2).2 ⟨c, hcW, rfl⟩
    obtain ⟨k, hk, hkW⟩ := trio_orbit hM W hW
    refine ⟨g * k, ?_, ?_⟩
    · have h1 : conjSub g⁻¹ V0 = conjSub k V0 := hWsub.symm.trans hkW
      have h2 := mem_normalizer_of_conjSub_eq h1
      rwa [inv_inv] at h2
    · intro h
      apply hgH
      have e : g = (g * k) * k⁻¹ := by group
      rw [e]
      exact Hj.mul_mem h (Hj.inv_mem hk)

theorem basePt_mem_X5 : basePt ∈ X5 := ⟨1, M3.one_mem, one_smul _ _⟩

theorem ncard_X5 (hF : J4Facts) : X5.ncard = 5 := by
  have hM := hF.mat
  have h1 : X5.ncard ≤ 6 := by
    have h := Set.ncard_le_ncard X5_subset (Set.toFinite _)
    have h' := Set.ncard_insert_le basePt BV
    have := ncard_BV_le hF
    omega
  have h2 : X5.ncard % 4 = 1 :=
    orbit_ncard_mod_four_J hF M3 ((Eg_le_D hM).trans D_le_M3)
  obtain ⟨n, hn, hnH⟩ := exists_mem_normalizer_not_mem_Hj hF
  have h3 : 2 ≤ X5.ncard := by
    have hsub : ({basePt, n • basePt} : Set (J ⧸ Hj)) ⊆ X5 := by
      intro w hw
      rcases hw with rfl | rfl
      · exact basePt_mem_X5
      · exact ⟨n, hn, rfl⟩
    have hne : basePt ≠ n • basePt := fun h => hnH (smul_basePt_eq_self_iff.mp h.symm)
    calc 2 = ({basePt, n • basePt} : Set (J ⧸ Hj)).ncard := (Set.ncard_pair hne).symm
      _ ≤ X5.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem orbit_M3_eq : MulAction.orbit ↥M3 (basePt : J ⧸ Hj) = X5 := by
  ext w
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, m.2, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩

theorem card_M3 (hF : J4Facts) : Nat.card ↥M3 = 660602880 := by
  have hM := hF.mat
  have hfix : ∀ g : J, g • (basePt : J ⧸ Hj) = basePt ↔ g ∈ Hj := fun g => smul_basePt_eq_self_iff
  have h := card_eq_orbit_mul_inf M3 Hj basePt hfix
  rw [orbit_M3_eq, Nat.card_coe_set_eq, ncard_X5 hF] at h
  have hNV : M3 ⊓ Hj = NV := inf_comm _ _
  rw [hNV] at h
  have h2 := card_mul_relIndex Hj NV NV_le_Hj
  rw [(idx_eq hM).1, card_Hj hF] at h2
  rw [h]
  generalize Nat.card ↥NV = c at h2 ⊢
  omega

theorem D5_eq_X5 (hF : J4Facts) : D5 = X5 := by
  have hM := hF.mat
  have hsub : D5 ⊆ X5 := fun w ⟨d, hd, h⟩ => ⟨d, D_le_M3 hd, h⟩
  have hmod : D5.ncard % 4 = 1 := orbit_ncard_mod_four_J hF _ (Eg_le_D hM)
  have hle : D5.ncard ≤ 5 := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_X5 hF).le
  have hbase : basePt ∈ D5 := ⟨1, (Subgroup.centralizer (V0 : Set J)).one_mem, one_smul _ _⟩
  have hcases : D5.ncard = 1 ∨ D5.ncard = 5 := by omega
  rcases hcases with h1 | h5
  · exfalso
    have hDH : Subgroup.centralizer (V0 : Set J) ≤ Hj := by
      intro d hd
      have hdmem : d • (basePt : J ⧸ Hj) ∈ D5 := ⟨d, hd, rfl⟩
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
      rw [ha] at hbase hdmem
      rw [Set.mem_singleton_iff] at hbase hdmem
      exact smul_basePt_eq_self_iff.mp (hdmem.trans hbase.symm)
    have hcD : Nat.card ↥(Subgroup.centralizer (V0 : Set J)) = 786432 := by
      have : Hj ⊓ Subgroup.centralizer (V0 : Set J) = Subgroup.centralizer (V0 : Set J) :=
        inf_eq_right.2 hDH
      have h := card_CV hF
      unfold CV at h
      rwa [this] at h
    have hDM : M3 ⊓ Subgroup.centralizer (V0 : Set J) = Subgroup.centralizer (V0 : Set J) :=
      inf_eq_right.2 D_le_M3
    have hidx := index_centralizer_eq V0 M3 (le_refl _)
    have hrange : Nat.card ↥((J4Rad.conjAut V0 M3 (le_refl _)).range) ≤ 168 := by
      rw [← card_mulAut_V0 hM]
      exact Subgroup.card_le_card_group _
    have hmul := card_mul_relIndex M3 (M3 ⊓ Subgroup.centralizer (V0 : Set J)) inf_le_left
    rw [hDM] at hidx hmul
    rw [hidx, hcD, card_M3 hF] at hmul
    have : Nat.card ↥((J4Rad.conjAut V0 M3 (le_refl _)).range) * 786432 = 660602880 := by
      rw [mul_comm]
      exact hmul
    generalize Nat.card ↥((J4Rad.conjAut V0 M3 (le_refl _)).range) = r at this hrange
    omega
  · exact Set.eq_of_subset_of_ncard_le hsub (by rw [h5, ncard_X5 hF]) (Set.toFinite _)

theorem E_transitive_X5 (hF : J4Facts) {x y : J ⧸ Hj} (hx : x ∈ X5) (hxb : x ≠ basePt)
    (hy : y ∈ X5) (hyb : y ≠ basePt) : ∃ e ∈ Eg uJ 11, e • x = y := by
  have hM := hF.mat
  obtain ⟨m, hm, rfl⟩ := hx
  set S : Set (J ⧸ Hj) := {w | ∃ e ∈ Eg uJ 11, e • (m • basePt) = w} with hS
  have hSsub : S ⊆ X5 \ {basePt} := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨⟨e * m, M3.mul_mem ((Eg_le_D hM).trans D_le_M3 he) hm, by rw [mul_smul]⟩, ?_⟩
    intro h
    rw [Set.mem_singleton_iff] at h
    apply hxb
    have h' : m • basePt = e⁻¹ • basePt := by
      rw [← smul_left_cancel_iff e, smul_inv_smul, h]
    rw [h']
    exact (smul_basePt_eq_self_iff.mpr (Eg_le_Hj (Subgroup.inv_mem _ he)))
  have hcard : (X5 \ {basePt}).ncard = 4 := by
    rw [Set.ncard_sdiff_singleton_of_mem basePt_mem_X5, ncard_X5 hF]
  have h4 : 4 ≤ S.ncard := four_le_ncard_orbit hxb
  have heq : S = X5 \ {basePt} :=
    Set.eq_of_subset_of_ncard_le hSsub (by rw [hcard]; exact h4) (Set.toFinite _)
  have hyS : y ∈ S := by
    rw [heq]
    exact ⟨hy, hyb⟩
  exact hyS

end Str

end CFSG.Quasithin.J4Fam
