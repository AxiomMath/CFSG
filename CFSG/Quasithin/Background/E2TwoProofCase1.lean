module

public import CFSG.Quasithin.Background.E2TwoProofSwap
public import CFSG.Quasithin.Background.E2TwoProofAS
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Background.E2TwoProofAutT

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native B6

namespace E2P

theorem map_map_conj {G G' : Type*} [Group G] [Group G'] (f : G →* G') (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map f = (A.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem a38Types_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : A38Types X) :
    A38Types Y := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, hp, hp3, hPSL⟩
  · exact Or.inl ⟨n, IsPSL.of_mulEquiv e hn⟩
  · exact Or.inr (Or.inl ⟨n, IsSz.of_mulEquiv e hn⟩)
  · exact Or.inr (Or.inr (Or.inl (IsSporadic.of_mulEquiv e hJ)))
  · exact Or.inr (Or.inr (Or.inr ⟨p, hp, hp3, IsPSL.of_mulEquiv e hPSL⟩))

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M : Subgroup Γ}

namespace Setting

variable {L : Subgroup (E2.StarQuot M H)} {K : Subgroup Γ}

theorem map_psi_tbar (S : Setting H T M L K) :
    ((T.subgroupOf H).map (barMap H)).map S.psi = E2.star M H T := by
  rw [Subgroup.map_map, star_def]
  congr 1
  exact MonoidHom.ext fun x => S.psi_barMap x

theorem map_psi_conj (S : Setting H T M L K) (g : ↥H ⧸ CFSG.pCore 2 ↥H) :
    ((kbar H K).map (MulAut.conj g).toMonoidHom).map S.psi =
      conjSub (S.psi g) L := by
  rw [map_map_conj, S.map_psi_kbar]
  rfl

namespace SwapData

variable {tb : ↥H ⧸ CFSG.pCore 2 ↥H}

theorem twoConj (D : SwapData H T K tb) (S : Setting H T M L K) :
    TwoConj (E2.star M H T) L (S.psi tb) := by
  have hinj := psi_injective D S
  have hmem : ∀ sb ∈ (T.subgroupOf H).map (barMap H), S.psi sb ∈ E2.star M H T := fun sb hsb => by
    rw [← S.map_psi_tbar]
    exact ⟨sb, hsb, rfl⟩
  have hconj : ∀ s ∈ E2.star M H T, conjSub s L = L ∨ conjSub s L = conjSub (S.psi tb) L := by
    intro s hs
    rw [← S.map_psi_tbar] at hs
    obtain ⟨sb, hsb, rfl⟩ := hs
    have h1 : (kbar H K).map (MulAut.conj sb).toMonoidHom ∈
        conjSubgroupsBy ((T.subgroupOf H).map (barMap H)) (kbar H K) := ⟨sb, hsb, rfl⟩
    rw [D.conjs] at h1
    rcases h1 with h1 | h1
    · left
      rw [← S.map_psi_conj, h1, S.map_psi_kbar]
    · right
      rw [← S.map_psi_conj, h1, S.map_psi_conj]
  refine ⟨hmem tb D.mem, ?_, hconj, ?_, ?_⟩
  · intro heq
    apply D.not_mem
    have h1 : ((kbar H K).map (MulAut.conj tb).toMonoidHom).map S.psi = (kbar H K).map S.psi :=
      (S.map_psi_conj tb).trans (heq.trans S.map_psi_kbar.symm)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.map_injective hinj h1)
  · have h1 : (⁅kbar H K, (kbar H K).map (MulAut.conj tb).toMonoidHom⁆).map S.psi =
        ⁅L, conjSub (S.psi tb) L⁆ := by
      rw [Subgroup.map_commutator, S.map_psi_kbar, S.map_psi_conj]
    rw [← h1, D.comm, Subgroup.map_bot]
  · have hgen := S.factor.gen
    apply le_antisymm
    · rw [hgen]
      refine iSup₂_le fun s hs => ?_
      rcases hconj s hs with h | h <;> rw [h]
      · exact le_sup_left
      · exact le_sup_right
    · rw [hgen]
      refine sup_le ?_ ?_
      · have := le_iSup₂_of_le (f := fun s (_ : s ∈ E2.star M H T) => conjSub s L) 1
          (E2.star M H T).one_mem le_rfl
        rwa [conjSub_one] at this
      · exact le_iSup₂_of_le (f := fun s (_ : s ∈ E2.star M H T) => conjSub s L) (S.psi tb)
          (hmem tb D.mem) le_rfl

theorem types_L (D : SwapData H T K tb) (S : Setting H T M L K) :
    A38Types ↥L := by
  have hinj := psi_injective D S
  have e : ↥(kbar H K) ≃* ↥L :=
    ((kbar H K).equivMapOfInjective S.psi hinj).trans (MulEquiv.subgroupCongr S.map_psi_kbar)
  exact a38Types_of_mulEquiv e D.types

end SwapData

omit [Finite Γ] in
theorem map_subtype_conj (A : Subgroup ↥H) (t₀ : ↥H) :
    (A.map (MulAut.conj t₀).toMonoidHom).map H.subtype =
      CFSG.Quasithin.cjSub (t₀ : Γ) (A.map H.subtype) := by
  rw [map_map_conj]
  rfl

theorem cases_of_not_normal (hF : E22Families)
    (h38 : A38ForSQTKCat) (S : Setting H T M L K) (hLn : ¬ L.Normal) :
    E2.E22CasesNoN H T M K := by
  have : Finite (E2.StarQuot M H) := finite_starQuot M H
  obtain ⟨tb, D⟩ := S.exists_swapData h38 hLn
  have h2 := D.twoConj S
  have hTypes := D.types_L S
  have hfac := S.factor
  have hAS := hfac.asHyp_autOn
  have e := hfac.innEquiv
  obtain ⟨t₀, ht₀, htb⟩ := D.mem
  have htT : (t₀ : Γ) ∈ T := Subgroup.mem_subgroupOf.mp ht₀
  have hpsi : S.psi tb = starMap M H t₀ := by rw [← htb, S.psi_barMap]
  have hMK : E2.star M H (M ⊓ K) = E2.star M H M ⊓ L := by
    rw [star_inf_M, S.star_eq]
  have hTK : E2.star M H (T ⊓ K) = E2.star M H T ⊓ L := by
    rw [star_inf_T S.minPar.isSylow (subnormal_of_mem_cComp S.cComp) S.le, S.star_eq]
  have hne : CFSG.Quasithin.cjSub (t₀ : Γ) K ≠ K := by
    intro heq
    apply D.not_mem
    have hK₀ : (K.subgroupOf H).map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le S.le
    have h1 : ((K.subgroupOf H).map (MulAut.conj t₀).toMonoidHom).map H.subtype =
        (K.subgroupOf H).map H.subtype := by
      rw [map_subtype_conj, hK₀, heq]
    have h3 := Subgroup.map_injective H.subtype_injective h1
    have h4 : ((K.subgroupOf H).map (MulAut.conj t₀).toMonoidHom).map (barMap H) =
        (kbar H K).map (MulAut.conj tb).toMonoidHom := by
      rw [map_map_conj, ← htb]
      rfl
    rw [h3] at h4
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h4.symm
  have hMeq : M = (M ⊓ K) ⊔ CFSG.Quasithin.cjSub (t₀ : Γ) (M ⊓ K) ⊔ T := by
    have hMH : M ≤ H := S.minPar.maximal.1.le
    have hY := h2.M_eq hfac
    rw [hpsi, ← hMK] at hY
    have hA : E2.star M H (M ⊓ K) = ((M ⊓ K).subgroupOf H).map (starMap M H) := rfl
    have hC : conjSub (starMap M H t₀) (E2.star M H (M ⊓ K)) =
        (((M ⊓ K).subgroupOf H).map (MulAut.conj t₀).toMonoidHom).map (starMap M H) := by
      rw [map_map_conj]
      rfl
    have hT' : E2.star M H T = (T.subgroupOf H).map (starMap M H) := rfl
    rw [hC, hA, hT', ← Subgroup.map_sup, ← Subgroup.map_sup] at hY
    have hle : M.subgroupOf H ≤ ((M ⊓ K).subgroupOf H ⊔
        ((M ⊓ K).subgroupOf H).map (MulAut.conj t₀).toMonoidHom ⊔ T.subgroupOf H) := by
      have hcomap : M.subgroupOf H ≤ (E2.star M H M).comap (starMap M H) :=
        Subgroup.le_comap_map _ _
      rw [hY, Subgroup.comap_map_eq] at hcomap
      refine hcomap.trans (sup_le le_rfl ?_)
      rw [ker_starMap]
      have hJ := D.kerIn_eq S
      have hP : (kerIn M H).subgroupOf H ≤ T.subgroupOf H := by
        rw [hJ]
        have h5 := pCoreOf_two_le_of_isSylowTwoOf S.minPar.subgroupOf.isSylow
        rw [pCoreOf_top] at h5
        have h6 : (pCoreOf 2 H).subgroupOf H = CFSG.Open.pCore 2 ↥H :=
          Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
        rw [h6]
        exact h5
      exact hP.trans le_sup_right
    apply le_antisymm
    · have := Subgroup.map_mono (f := H.subtype) hle
      rw [Subgroup.map_subgroupOf_eq_of_le hMH, Subgroup.map_sup, Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hMH), map_subtype_conj,
        Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hMH),
        Subgroup.map_subgroupOf_eq_of_le S.minPar.isSylow.1] at this
      exact this
    · refine sup_le (sup_le inf_le_left ?_) S.minPar.le
      intro x hx
      rw [CFSG.Quasithin.mem_cjSub] at hx
      have htM : (t₀ : Γ) ∈ M := S.minPar.le htT
      have := M.mul_mem (M.mul_mem htM hx.1) (M.inv_mem htM)
      simpa [mul_assoc] using this
  unfold E2.E22CasesNoN
  simp only []
  rw [S.star_eq, hMK, hTK]
  refine Or.inl ⟨D.kerIn_eq S, (t₀ : Γ), htT, hne, hMeq, ?_⟩
  rw [inf_comm (E2.star M H M) L]
  rcases hTypes with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, hp, hp3, hPSL⟩
  ·
    have hn2 : 2 ≤ n := by
      obtain ⟨⟨-, hn1, -, hne2, -⟩, -⟩ := hn
      by_contra h
      have : n = 1 := by omega
      subst this
      exact hne2 rfl
    have hB := hF.bender _ _ _ _ hAS n ⟨hn2, Or.inl (IsPSL.of_mulEquiv e hn)⟩
    refine Or.inl ⟨n, hn2, Or.inl hn, ?_⟩
    rw [inf_comm]
    exact h2.isBorelIn_of_aut hfac hB
  ·
    have hn2 : 2 ≤ n := by
      obtain ⟨-, a, ha, -, -, -, hf, -⟩ := hn
      omega
    have hB := hF.bender _ _ _ _ hAS n ⟨hn2, Or.inr (Or.inl (IsSz.of_mulEquiv e hn))⟩
    refine Or.inl ⟨n, hn2, Or.inr hn, ?_⟩
    rw [inf_comm]
    exact h2.isBorelIn_of_aut hfac hB
  ·
    exact (false_of_asc86b hAS (hF.sporTen .J1 (by unfold SporTen; tauto))
      (IsSporadic.of_mulEquiv e hJ)).elim
  ·
    by_cases hp5 : p = 5
    · subst hp5
      obtain ⟨h1, hB⟩ := (hF.alt _ _ _ _ hAS).1 (Or.inr (IsPSL.of_mulEquiv e hPSL))
      refine Or.inl ⟨2, le_rfl, Or.inl (IsPSL.of_mulEquiv e.symm h1), ?_⟩
      rw [inf_comm]
      exact h2.isBorelIn_of_aut hfac hB
    · have hp9 : p ≠ 9 := fun h => by subst h; norm_num at hp
      obtain ⟨-, hcong, hC, hA⟩ := hF.oddL2 _ _ _ _ hAS p 1 hp (by omega) (Or.inl rfl)
        (by rwa [pow_one]) (by rwa [pow_one]) (IsPSL.of_mulEquiv e hPSL)
      refine Or.inr ⟨p, hp, by simpa using hcong, hPSL, ?_, ?_⟩
      · rw [inf_comm]
        exact h2.inf_eq_centralizer_of_aut hfac hC
      · rw [← hfac.autCard_eq]
        exact hA

end Setting

end E2P

end CFSG.Quasithin
