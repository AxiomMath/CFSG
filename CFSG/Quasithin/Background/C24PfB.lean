module

public import CFSG.Quasithin.Background.C22PfB
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.Background.C2PushBlocks
public import CFSG.Quasithin.EmptyFaithful.S151TCCh
public import CFSG.Quasithin.EmptyFaithful.A38c10MSc
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Quot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace C24Pf

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjByElt_inv_conjByElt (x : G) (L : Subgroup G) :
    conjByElt x⁻¹ (conjByElt x L) = L := by
  ext y
  rw [mem_conjByElt, mem_conjByElt]
  simp [mul_assoc]

theorem le_normalizer_of_commutator_le {H L L' : Subgroup G} (hL : L ∈ cComp H)
    (hc : ⁅L, L'⁆ ≤ pCoreOf 2 H) : L' ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hON : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) :=
    P134.pCoreOf_le_normalizer_of_mem_cComp hL
  intro y hy
  set K := L.map (MulAut.conj y).toMonoidHom with hK
  have hKp : ⁅K, K⁆ = K := by rw [hK, ← Subgroup.map_commutator, perfect_of_mem_cComp hL]
  have hKL : K ≤ L ⊔ pCoreOf 2 H := by
    rintro _ ⟨l, hl, rfl⟩
    have e : (MulAut.conj y).toMonoidHom l = (y * l * y⁻¹ * l⁻¹) * l := by
      simp [MulAut.conj_apply]
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right (hc ?_)) (Subgroup.mem_sup_left hl)
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hy hl
  have hle := C2Push.le_of_perfect_le_sup (pCoreOf_isPGroup 2 H) hON hKp hKL
  exact C22Pf.mem_normalizer_of_conj_mem fun l hl => hle ⟨l, hl, by simp [MulAut.conj_apply]⟩

theorem center_eq_bot (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hS : ∀ (X : Type) [Group X], A38Types X → IsSimpleGroup X) {H L : Subgroup G}
    (hH : IsSQTKIn H) (hL : L ∈ cComp H) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    {h : G} (hh : h ∈ H) (hhL : h ∉ Subgroup.normalizer (L : Set G)) :
    Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
  have hQ := SQTKHyp.of_sqtkGroup ↥H hH
  rcases (hA38 _ hQ (modO2Image H L) (modO2Image_mem_cComp hL)).1 with hn | ⟨htype, -⟩
  · exfalso
    apply hhL
    refine C22Pf.mem_normalizer_of_mk_cComp hL (x := ⟨h, hh⟩) ?_
    exact Subgroup.mem_normalizer_iff.mpr fun n =>
      ⟨fun hn' => hn.conj_mem n hn' _, fun hn' => by
        have := hn.conj_mem _ hn' (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨h, hh⟩)⁻¹
        simpa [mul_assoc] using this⟩
  · have := hS _ htype
    obtain ⟨e⟩ := modO2_mulEquiv hL
    have := hLq.2.1
    have : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))).nontrivial
    have : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
      IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) with
      hc | hc
    · exact hc
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (QuotientGroup.eq.mpr (by rw [hc]; trivial))

theorem inf_pCoreOf_le {H K : Subgroup G} (hKH : K ≤ H) : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun k hk => ?_)
    ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 H (hKH hk)⟩

theorem charTwo_conjClosure_sup (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hS : ∀ (X : Type) [Group X], A38Types X → IsSimpleGroup X) {H R L : Subgroup G}
    (hH : IsSQTKIn H) (hR : IsTwoRadicalIn H R) (hL : L ∈ cComp H) (hLc : CharTwo L)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) : CharTwo (conjClosure L R ⊔ R) := by
  have hR2 : IsPGroup 2 ↥R := hR.isPGroup
  have hRH : R ≤ H := hR.1
  have hLH : L ≤ H := le_of_mem_cComp hL
  by_cases hRN : R ≤ Subgroup.normalizer (L : Set G)
  · have hcc : conjClosure L R = L := by
      refine le_antisymm (conjClosure_le fun r hr l hl => ?_) (le_conjClosure L R)
      exact (Subgroup.mem_normalizer_iff.mp (hRN hr) l).mp hl
    rw [hcc]
    exact A38c10.MS.charTwo_sup_of_le hLc hR2 hRN le_rfl ((pCoreOf_le 2 L).trans le_sup_left)
  · obtain ⟨ρ, hρR, hρN⟩ := IsConcreteLE.not_le_iff_exists.mp hRN
    obtain ⟨T, hT, hRT⟩ := EscapingLocal.exists_isSylowTwoOf_ge hRH hR2
    obtain ⟨-, hcase⟩ := a3Orbits_of_a37_a38 (G := G) hA37 hA38 H T L hH hT hL
    rcases hcase with hTN | ⟨t, -, -, hTL, hcomm, -, -⟩
    · exact absurd (hTN ρ (hRT hρR)) hρN
    have hρne : conjByElt ρ L ≠ L := fun he =>
      hρN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he)
    have hmem : ∀ σ ∈ R, conjByElt σ L = L ∨ conjByElt σ L = conjByElt t L := by
      intro σ hσ
      have h1 : conjByElt σ L ∈ conjSubgroupsBy T L := ⟨σ, hRT hσ, rfl⟩
      rw [hTL] at h1
      exact h1
    have hρt : conjByElt ρ L = conjByElt t L := (hmem ρ hρR).resolve_left hρne
    have hLρ : conjByElt ρ L ∈ cComp H := by
      have h1 := cComp_map_mulEquiv (MulAut.conj ρ) hL
      have h2 : H.map (MulAut.conj ρ).toMonoidHom = H :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hRH hρR))
      rwa [h2] at h1
    have hc : ⁅L, conjByElt ρ L⁆ ≤ pCoreOf 2 H := hρt ▸ hcomm
    have hN1 : conjByElt ρ L ≤ Subgroup.normalizer (L : Set G) :=
      le_normalizer_of_commutator_le hL hc
    have hN2 : L ≤ Subgroup.normalizer ((conjByElt ρ L : Subgroup G) : Set G) :=
      le_normalizer_of_commutator_le hLρ (by rw [Subgroup.commutator_comm]; exact hc)
    have hcL : ⁅L, conjByElt ρ L⁆ ≤ L := by
      rw [Subgroup.commutator_le]
      intro l hl y hy
      rw [commutatorElement_def]
      have h1 : y * l⁻¹ * y⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hN1 hy) _).mp (L.inv_mem hl)
      have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
      rw [e]
      exact L.mul_mem hl h1
    have hcL' : ⁅L, conjByElt ρ L⁆ ≤ conjByElt ρ L := by
      rw [Subgroup.commutator_le]
      intro l hl y hy
      rw [commutatorElement_def]
      have h1 : l * y * l⁻¹ ∈ conjByElt ρ L :=
        (Subgroup.mem_normalizer_iff.mp (hN2 hl) _).mp hy
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy)
    refine S151TC.charTwo_conjClosure_sup_of_two ρ hρR hR2 (perfect_of_mem_cComp hL) hLc hLq
      (center_eq_bot hA38 hS hH hL hLq (hRH hρR) hρN) (fun σ hσ => ?_) ?_
    · rcases hmem σ hσ with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans hρt.symm)
    · exact le_inf ((le_inf hcL hc).trans (inf_pCoreOf_le hLH))
        ((le_inf hcL' hc).trans (inf_pCoreOf_le (le_of_mem_cComp hLρ)))

end C24Pf

end CFSG.Quasithin
