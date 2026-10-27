
module

public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem A38Types.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : A38Types X) :
    A38Types Y := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, hp, hp3, hPSL⟩
  · exact Or.inl ⟨n, IsPSL.of_mulEquiv e hn⟩
  · exact Or.inr (Or.inl ⟨n, IsSz.of_mulEquiv e hn⟩)
  · exact Or.inr (Or.inr (Or.inl (IsSporadic.of_mulEquiv e hJ)))
  · exact Or.inr (Or.inr (Or.inr ⟨p, hp, hp3, IsPSL.of_mulEquiv e hPSL⟩))

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem commutator_le_of_ne_of_quotient (N : Subgroup X) [N.Normal] (hN : Group.IsSolvable N)
    (h37 : A37Statement (X ⧸ N)) {L₁ L₂ : Subgroup X} (h₁ : L₁ ∈ cComp (⊤ : Subgroup X))
    (h₂ : L₂ ∈ cComp (⊤ : Subgroup X)) (hne : L₁ ≠ L₂) : ⁅L₁, L₂⁆ ≤ N := by
  have hker : Group.IsSolvable (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']; exact hN
  have hb₁ := map_mem_cComp_top (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hker h₁
  have hb₂ := map_mem_cComp_top (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hker h₂
  have hne' : L₁.map (QuotientGroup.mk' N) ≠ L₂.map (QuotientGroup.mk' N) := fun h =>
    hne (map_injOn_cComp_top (QuotientGroup.mk' N) hker h₁ h₂ h)
  have h := h37 _ hb₁ _ hb₂ hne'
  rw [← Subgroup.map_commutator] at h
  rw [← QuotientGroup.ker_mk' N]
  exact (Subgroup.map_eq_bot_iff _).mp h

theorem normal_of_normal_map_of_mem_cComp (N : Subgroup X) [N.Normal] (hN : Group.IsSolvable N)
    {L : Subgroup X} (hL : L ∈ cComp (⊤ : Subgroup X))
    (hn : (L.map (QuotientGroup.mk' N)).Normal) : L.Normal := by
  have h3 := cComp_commutator_perfectCore hL le_top hN Subgroup.le_normalizer_of_normal
  have hpre : L ⊔ N = (L.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hnormLN : (L ⊔ N).Normal := by
    rw [hpre]
    exact Subgroup.Normal.comap hn _
  have h1 := normalizer_le_normalizer_perfectCore (L ⊔ N)
  rw [h3.2, Subgroup.normalizer_eq_top_iff.mpr hnormLN] at h1
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)

end Abstract

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_pCoreOf_two (H : Subgroup G) : Group.IsSolvable ↥(pCoreOf 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have : Group.IsNilpotent ↥(pCoreOf 2 H) := h.isNilpotent
  infer_instance

theorem commutator_le_pCoreOf_of_ne {H L₁ L₂ : Subgroup G}
    (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (h₁ : L₁ ∈ cComp H) (h₂ : L₂ ∈ cComp H)
    (hne : L₁ ≠ L₂) : ⁅L₁, L₂⁆ ≤ pCoreOf 2 H := by
  have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hne' : L₁.subgroupOf H ≠ L₂.subgroupOf H := fun h =>
    hne ((cComp_subgroupOf_bijOn H).injOn h₁ h₂ h)
  have h := commutator_le_of_ne_of_quotient (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H) h37
    (subgroupOf_mem_cComp h₁) (subgroupOf_mem_cComp h₂) hne'
  have h' := Subgroup.map_mono (f := H.subtype) h
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp h₁),
    Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp h₂)] at h'
  have hP : (CFSG.pCore 2 ↥H).map H.subtype = pCoreOf 2 H := by
    rfl
  rwa [hP] at h'

theorem le_normalizer_of_mem_cComp {H L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ cComp H)
    (h₂ : L₂ ∈ cComp H) : L₂ ≤ Subgroup.normalizer (L₁ : Set G) := by
  obtain ⟨hle₁, hn₁⟩ := cComp_normal_span_of_le h₁
  obtain ⟨hle₂, -⟩ := cComp_normal_span_of_le h₂
  exact hle₂.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hle₁).mp hn₁)

theorem commutator_le_pCoreOf_inf_of_le_sq {H L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ cComp H)
    (h₂ : L₂ ∈ cComp H) (hc : ⁅L₁, L₂⁆ ≤ pCoreOf 2 H) :
    ⁅L₁, L₂⁆ ≤ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂ ∧ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂ ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn₁ := le_normalizer_of_mem_cComp h₁ h₂
  have hn₂ := le_normalizer_of_mem_cComp h₂ h₁
  have hc₁ : ⁅L₁, L₂⁆ ≤ L₁ := Subgroup.le_normalizer_iff_commutator_le_left.mp hn₁
  have hc₂ : ⁅L₁, L₂⁆ ≤ L₂ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hn₂
  have hLH₁ : L₁ ≤ H := le_of_mem_cComp h₁
  have hLH₂ : L₂ ≤ H := le_of_mem_cComp h₂
  have hpH : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hnormO : ∀ {L : Subgroup G}, L ≤ H → L ≤ Subgroup.normalizer ((L ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
    intro L hLH x hx
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, ?_⟩
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hLH hx)
  have hle₁ : L₁ ⊓ pCoreOf 2 H ≤ pCoreOf 2 L₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (hnormO hLH₁)
      (hpH.to_le inf_le_right)
  have hle₂ : L₂ ⊓ pCoreOf 2 H ≤ pCoreOf 2 L₂ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (hnormO hLH₂)
      (hpH.to_le inf_le_right)
  refine ⟨le_inf (fun x hx => hle₁ ⟨hc₁ hx, hc hx⟩) (fun x hx => hle₂ ⟨hc₂ hx, hc hx⟩), ?_⟩
  exact inf_le_left.trans (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp h₁))

theorem lemma_1_2_1_two_of_a3 {H L₁ L₂ : Subgroup G}
    (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (h₁ : L₁ ∈ cComp H) (h₂ : L₂ ∈ cComp H)
    (hne : L₁ ≠ L₂) :
    ⁅L₁, L₂⁆ ≤ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂ ∧ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂ ≤ pCoreOf 2 H :=
  commutator_le_pCoreOf_inf_of_le_sq h₁ h₂ (commutator_le_pCoreOf_of_ne h37 h₁ h₂ hne)

theorem lemma_1_2_1_two (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) {H L₁ L₂ : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (h₁ : L₁ ∈ cComp H) (h₂ : L₂ ∈ cComp H) (hne : L₁ ≠ L₂) :
    ⁅L₁, L₂⁆ ≤ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂ ∧ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂ ≤ pCoreOf 2 H :=
  lemma_1_2_1_two_of_a3 (h37 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot hK hs hnab hH)) h₁ h₂ hne

omit [Finite G] in
theorem map_conj_mem_cComp {H L : Subgroup G} (hL : L ∈ cComp H) {h : G} (hh : h ∈ H) :
    L.map (MulAut.conj h).toMonoidHom ∈ cComp H := by
  have h1 := cComp_map_mulEquiv (MulAut.conj h) hL
  have h2 : H.map (MulAut.conj h).toMonoidHom = H := A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer hh)
  rwa [h2] at h1

omit [Finite G] in
theorem modO2Image_conj {H L : Subgroup G} (h : ↥H) :
    modO2Image H (L.map (MulAut.conj (h : G)).toMonoidHom) =
      (modO2Image H L).map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) h)).toMonoidHom := by
  unfold modO2Image
  have h1 : (L.map (MulAut.conj (h : G)).toMonoidHom).subgroupOf H =
      (L.subgroupOf H).map (MulAut.conj h).toMonoidHom := by
    ext x
    rw [Subgroup.mem_subgroupOf, A38.mem_map_conj, A38.mem_map_conj, Subgroup.mem_subgroupOf]
    rfl
  rw [h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem lemma_1_2_1_three_of_a3_sq {H L : Subgroup G}
    (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (h38 : A38Part3 (↥H ⧸ CFSG.pCore 2 ↥H))
    (hL : L ∈ cComp H) :
    (L.subgroupOf H).Normal ∨
      (Set.ncard (conjSubgroupsBy H L) = 2 ∧ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have hLb := modO2Image_mem_cComp hL
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  obtain ⟨hL1, -⟩ := h38 _ hLb
  rcases hL1 with hnorm | ⟨htypes, t', ht'n, -, -, hcl'⟩
  · left
    exact normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)
      (subgroupOf_mem_cComp hL) hnorm
  · right
    refine ⟨?_, ?_⟩
    · obtain ⟨th, hth⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) t'
      set Lb := modO2Image H L with hLb'
      have hL₂ : L.map (MulAut.conj (th : G)).toMonoidHom ∈ cComp H := map_conj_mem_cComp hL th.2
      have hL₂b : modO2Image H (L.map (MulAut.conj (th : G)).toMonoidHom) =
          Lb.map (MulAut.conj t').toMonoidHom := by
        rw [modO2Image_conj th, hth]
      have hne : L ≠ L.map (MulAut.conj (th : G)).toMonoidHom := by
        intro h
        apply ht'n
        have : Lb.map (MulAut.conj t').toMonoidHom = Lb := by
          rw [← hL₂b, ← h]
        exact A38.map_conj_eq_iff.mp this
      have hset : conjSubgroupsBy H L = {L, L.map (MulAut.conj (th : G)).toMonoidHom} := by
        ext K'
        constructor
        · rintro ⟨h, hhH, rfl⟩
          have hLh : L.map (MulAut.conj h).toMonoidHom ∈ cComp H := map_conj_mem_cComp hL hhH
          have hb : modO2Image H (L.map (MulAut.conj h).toMonoidHom) =
              Lb.map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨h, hhH⟩)).toMonoidHom :=
            modO2Image_conj ⟨h, hhH⟩
          set g := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨h, hhH⟩ with hg
          have hLg := A38.cComp_conj (t := g) hLb
          have hLt' := A38.cComp_conj (t := t') hLb
          have hle : Lb.map (MulAut.conj g).toMonoidHom ≤ Lb ⊔ Lb.map (MulAut.conj t').toMonoidHom := by
            rw [← hcl']
            intro x hx
            rw [A38.mem_map_conj] at hx
            have := mem_conjClosure (Subgroup.mem_top g) hx
            simpa [mul_assoc] using this
          rcases A38.eq_or_eq_of_le_sup h37 hLg hLb hLt' hle with h1 | h1
          · left
            exact (modO2Image_injOn H) hLh hL (by rw [hb, h1])
          · right
            exact (modO2Image_injOn H) hLh hL₂ (by rw [hb, hL₂b, h1])
        · rintro (rfl | rfl)
          · exact ⟨1, H.one_mem, (by ext x; simp)⟩
          · exact ⟨th, th.2, rfl⟩
      rw [hset]
      exact Set.ncard_pair hne
    · obtain ⟨e⟩ := modO2_mulEquiv hL
      exact A38Types.of_mulEquiv e.symm htypes

theorem lemma_1_2_1_three (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h38 : A38ForSQTK) {H L : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) :
    (L.subgroupOf H).Normal ∨
      (Set.ncard (conjSubgroupsBy H L) = 2 ∧ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)) :=
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hK hs hnab hH
  lemma_1_2_1_three_of_a3_sq (h37 _ hQ) (h38 _ hQ) hL

theorem lemma_1_2_4_unique {H S B L₁ L₂ : Subgroup G}
    (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (hB : B ∈ lFamily S) (h₁ : L₁ ∈ cComp H)
    (h₂ : L₂ ∈ cComp H) (hB₁ : B ≤ L₁) (hB₂ : B ≤ L₂) : L₁ = L₂ := by
  by_contra hne
  have hc := commutator_le_pCoreOf_of_ne h37 h₁ h₂ hne
  have hB' : B ∈ cComp (B ⊔ S) := hB
  have hBB : ⁅B, B⁆ ≤ pCoreOf 2 H := (Subgroup.commutator_mono hB₁ hB₂).trans hc
  rw [perfect_of_mem_cComp hB'] at hBB
  have := isSolvable_pCoreOf_two H
  exact not_isSolvable_of_mem_cComp hB'
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hBB)
      (Subgroup.inclusion_injective hBB))

theorem lemma_1_2_4_existsUnique (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    {H S B : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hBH : B ≤ H)
    (hB : B ∈ lFamily S) : ∃! L, L ∈ cComp H ∧ B ≤ L := by
  obtain ⟨L, hL, hBL⟩ := lemma_1_2_4_exists hK hs hnab h37 h39 hH hS hBH hB
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hK hs hnab hH
  exact ⟨L, ⟨hL, hBL⟩, fun L' hL' => lemma_1_2_4_unique (h37 _ hQ) hB hL'.1 hL hL'.2 hBL⟩

theorem lemma_1_2_4_normal_of_a3_sq {H S B L : Subgroup G}
    (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (h38 : A38Part3 (↥H ⧸ CFSG.pCore 2 ↥H))
    (hS : IsSylowTwoOf S H) (hB : B ∈ lFamily S) (hBL : B ≤ L) (hL : L ∈ cComp H)
    (hSB : S ≤ Subgroup.normalizer (B : Set G)) : (L.subgroupOf H).Normal := by
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := by
    intro s hs'
    have hLs : L.map (MulAut.conj s).toMonoidHom ∈ cComp H := map_conj_mem_cComp hL (hS.1 hs')
    have hBs : B.map (MulAut.conj s).toMonoidHom = B := A38.map_conj_eq_iff.mpr (hSB hs')
    have hBLs : B ≤ L.map (MulAut.conj s).toMonoidHom := by
      rw [← hBs]
      exact Subgroup.map_mono hBL
    have := lemma_1_2_4_unique h37 hB hL hLs hBL hBLs
    exact A38.map_conj_eq_iff.mp this.symm
  have hLb := modO2Image_mem_cComp hL
  have hTb := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (QuotientGroup.mk'_surjective _)
  obtain ⟨-, hL2⟩ := h38 _ hLb
  rcases hL2 _ hTb with ⟨hnorm, -, -⟩ | ⟨t, htT, htn, -⟩
  · exact normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)
      (subgroupOf_mem_cComp hL) hnorm
  · exfalso
    apply htn
    obtain ⟨s', hs'T, rfl⟩ := htT
    have hs'N : s' ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have hsG : (s' : G) ∈ S := hs'T
      have := (Subgroup.mem_normalizer_iff.mp (hSL hsG) (x : G))
      simpa using this
    exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
      ⟨s', hs'N, rfl⟩

theorem lemma_1_2_4_normal (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {H S B L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hB : B ∈ lFamily S)
    (hBL : B ≤ L) (hL : L ∈ cComp H) (hSB : S ≤ Subgroup.normalizer (B : Set G)) :
    (L.subgroupOf H).Normal :=
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hK hs hnab hH
  lemma_1_2_4_normal_of_a3_sq (h37 _ hQ) (h38 _ hQ) hS hB hBL hL hSB

end Ambient

end CFSG.Quasithin
