module

public import CFSG.Sporadic.HNOddCore.OrbitCert

public section

namespace CFSG.Sporadic.HNOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native

variable {N : ℕ} {G : Type*} [Group G] [MulAction G (Fin N)]

theorem smul_preimage_of_image {S : Set (Fin N)} {g : G} (h : ∀ x ∈ S, g • x ∈ S) :
    ∀ x ∈ S, g⁻¹ • x ∈ S := by
  have := perm_preimage_of_image (g := MulAction.toPerm g) h
  intro x hx
  simpa using this x hx

theorem smul_pt_of_restrict {F : Array ℕ} (hF : PtList N F) {pos : Array ℕ}
    (hpos : pointsOK N F pos = true) {T s : Array ℕ} {g : G}
    (hT : PRep N T (MulAction.toPerm g))
    (hpres : ∀ k : Fin F.size, ∃ l : Fin F.size, g • hF.pt k = hF.pt l)
    (hs : peq F.size (restrictTab T F pos) s = true) :
    ∀ k : Fin F.size, ∃ h : s[(k : ℕ)]! < F.size, g • hF.pt k = hF.pt ⟨s[(k : ℕ)]!, h⟩ := by
  intro k
  obtain ⟨l, hl⟩ := hpres k
  have hk : (k : ℕ) < F.size := k.2
  have h1 : (restrictTab T F pos)[(k : ℕ)]! = pos[T[F[(k : ℕ)]!]!]! := by
    rw [restrictTab, getElem!_pos _ _ (by simp [hk]), Array.getElem_map,
      ← getElem!_pos F (k : ℕ) hk]
  have h2 : T[F[(k : ℕ)]!]! = F[(l : ℕ)]! := by
    have := hT (hF.pt k)
    rw [MulAction.toPerm_apply, hl] at this
    exact this
  have h3 : (restrictTab T F pos)[(k : ℕ)]! = l := by
    rw [h1, h2]
    exact ((pointsOK_spec hpos).2 _ l.2).2
  have h4 : s[(k : ℕ)]! = l := by
    have := allBelowN_spec hs hk
    rw [beq_iff_eq] at this
    rw [← this, h3]
  refine ⟨by rw [h4]; exact l.2, ?_⟩
  rw [hl]
  congr 1
  exact Fin.ext h4.symm

theorem orbit_eq_of_cert {F : Array ℕ} (hF : PtList N F) {gs : ℕ → G} {gens : Array (Array ℕ)}
    (hact : ∀ s < gens.size, ∀ k : Fin F.size, ∃ h : (gens[s]!)[(k : ℕ)]! < F.size,
      gs s • hF.pt k = hF.pt ⟨(gens[s]!)[(k : ℕ)]!, h⟩)
    {L pos par lab : Array ℕ} (h : orbitCertOK F.size gens L pos par lab = true) :
    let hL := ptList_of_pointsOK (orbitCertOK_spec h).2.1
    MulAction.orbit (Subgroup.closure (Set.range fun s : Fin gens.size => gs s))
        (hF.pt (hL.pt ⟨0, (orbitCertOK_spec h).1⟩)) =
      hF.pt '' Set.range hL.pt := by
  intro hL
  obtain ⟨h0, hpts, htree, hcl⟩ := orbitCertOK_spec h
  set K := Subgroup.closure (Set.range fun s : Fin gens.size => gs s)
  apply Set.Subset.antisymm
  · have hgen : ∀ s : Fin gens.size, ∀ x ∈ hF.pt '' Set.range hL.pt,
        gs s • x ∈ hF.pt '' Set.range hL.pt := by
      rintro s _ ⟨_, ⟨i, rfl⟩, rfl⟩
      obtain ⟨hlt, heq⟩ := hcl i i.2 s s.2
      obtain ⟨hb, he⟩ := hact s s.2 (hL.pt i)
      refine ⟨hL.pt ⟨_, hlt⟩, ⟨_, rfl⟩, ?_⟩
      rw [he]
      congr 1
      apply Fin.ext
      simp only [PtList.pt_val]
      exact heq
    have hK : ∀ g ∈ K, ∀ x ∈ hF.pt '' Set.range hL.pt, g • x ∈ hF.pt '' Set.range hL.pt := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨s, rfl⟩ := hg
        exact hgen s
      | one => intro x hx; rwa [one_smul]
      | mul a b _ _ ha hb => intro x hx; rw [mul_smul]; exact ha _ (hb x hx)
      | inv a _ ha => exact smul_preimage_of_image ha
    rintro _ ⟨g, rfl⟩
    exact hK g g.2 _ ⟨_, ⟨_, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨⟨k, hk⟩, rfl⟩, rfl⟩
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact MulAction.mem_orbit_self _
      · obtain ⟨hp, hl, he⟩ := htree k hk hk0
        obtain ⟨g, hg⟩ := ih _ hp (lt_trans hp hk)
        have hg' : g • hF.pt (hL.pt ⟨0, h0⟩) = hF.pt (hL.pt ⟨par[k]!, lt_trans hp hk⟩) := hg
        have hσ : gs lab[k]! ∈ K := Subgroup.subset_closure ⟨⟨_, hl⟩, rfl⟩
        refine ⟨⟨gs lab[k]!, hσ⟩ * g, ?_⟩
        show (⟨gs lab[k]!, hσ⟩ * g) • hF.pt (hL.pt ⟨0, h0⟩) = hF.pt (hL.pt ⟨k, hk⟩)
        rw [mul_smul, hg']
        obtain ⟨hb, hs⟩ := hact _ hl (hL.pt ⟨par[k]!, lt_trans hp hk⟩)
        show gs lab[k]! • hF.pt (hL.pt ⟨par[k]!, lt_trans hp hk⟩) = hF.pt (hL.pt ⟨k, hk⟩)
        rw [hs]
        congr 1
        apply Fin.ext
        simp only [PtList.pt_val]
        exact he

end CFSG.Sporadic.HNOddCore
