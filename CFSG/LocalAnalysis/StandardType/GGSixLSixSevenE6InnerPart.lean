module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUExc
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny

section Inner

theorem ggClosure_xm_simple_eq_top {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*)
    [Field k] :
    Subgroup.closure {g | ∃ (i : Fin τ.rank) (c : k),
      g = hV.xm k (Pi.single i 1) c ∨ g = hV.xm k (-Pi.single i 1) c} = ⊤ := by
  set S := Subgroup.closure {g | ∃ (i : Fin τ.rank) (c : k),
    g = hV.xm k (Pi.single i 1) c ∨ g = hV.xm k (-Pi.single i 1) c}
  have hn : ∀ i, hV.nm k i ∈ S := fun i =>
    mul_mem (mul_mem (Subgroup.subset_closure ⟨i, _, Or.inl rfl⟩)
      (Subgroup.subset_closure ⟨i, _, Or.inr rfl⟩)) (Subgroup.subset_closure ⟨i, _, Or.inl rfl⟩)
  have hx : ∀ γ, IsRoot τ γ → ∀ c : k, hV.xm k γ c ∈ S := by
    intro γ hγ
    induction hγ with
    | basis j => exact fun c => Subgroup.subset_closure ⟨j, c, Or.inl rfl⟩
    | @reflect i v hv ih =>
      intro c
      obtain ⟨σ, hσ, h⟩ := hV.nm_conj_xm k hv i
      have e : hV.xm k (reflect τ i v) c = hV.nm k i * hV.xm k v (σ * c) * (hV.nm k i)⁻¹ := by
        rw [h, ← mul_assoc, hσ.mul_self, one_mul]
      rw [e]
      exact mul_mem (mul_mem (hn i) (ih _)) (inv_mem (hn i))
  rw [eq_top_iff, ← hV.iSup_rootGroup k]
  refine iSup₂_le fun γ hγ => ?_
  intro g hg
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hg
  exact hx γ hγ c

theorem ggPsiInnerDiag_E6_two_exists_centralizing {G : Type} [Group G] {n : ℕ}
    (ψ : (ggU .E6 n 1).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .E6 n 1).K) {c : G}
    (hc : GGPsiInnerDiag (ggU .E6 n 1).D ψ c) :
    ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  let ψ' : ↥(e6Data_valid.minGroup (GaloisField 2 1)) →* G := ψ
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  haveI : Subsingleton (GaloisField 2 1)ˣ :=
    (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, hcard])).1
  have hker' : ψ'.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 1)) := hker
  have hc' : GGPsiInnerDiag (e6Datum (GaloisField 2 1)) ψ' c := hc
  obtain ⟨g, hg, a, ha⟩ := PsiDiagChar.exists_char_E6 (k := GaloisField 2 1) ψ' hker' hc'
  have hpos : ∀ (i : Fin (e6Datum (GaloisField 2 1)).rank) (t : GaloisField 2 1),
      ψ' (e6Data_valid.xm (GaloisField 2 1) (Pi.single i 1) t) * (c * g) =
        (c * g) * ψ' (e6Data_valid.xm (GaloisField 2 1) (Pi.single i 1) t) := by
    intro i t
    have h := (ha i t).1
    rw [Subsingleton.elim (a i) 1, Units.val_one, one_mul] at h
    calc ψ' (e6Data_valid.xm (GaloisField 2 1) (Pi.single i 1) t) * (c * g)
        = (c * g) * ((c * g)⁻¹ * ψ' (e6Data_valid.xm (GaloisField 2 1) (Pi.single i 1) t)
            * (c * g)) := by group
      _ = (c * g) * ψ' (e6Data_valid.xm (GaloisField 2 1) (Pi.single i 1) t) :=
            congrArg (fun w => (c * g) * w) h
  have hneg : ∀ (i : Fin (e6Datum (GaloisField 2 1)).rank) (t : GaloisField 2 1),
      ψ' (e6Data_valid.xm (GaloisField 2 1) (-Pi.single i 1) t) * (c * g) =
        (c * g) * ψ' (e6Data_valid.xm (GaloisField 2 1) (-Pi.single i 1) t) := by
    intro i t
    have h := (ha i t).2
    rw [Subsingleton.elim (a i) 1, inv_one, Units.val_one, one_mul] at h
    calc ψ' (e6Data_valid.xm (GaloisField 2 1) (-Pi.single i 1) t) * (c * g)
        = (c * g) * ((c * g)⁻¹ * ψ' (e6Data_valid.xm (GaloisField 2 1) (-Pi.single i 1) t)
            * (c * g)) := by group
      _ = (c * g) * ψ' (e6Data_valid.xm (GaloisField 2 1) (-Pi.single i 1) t) :=
            congrArg (fun w => (c * g) * w) h
  refine ⟨g, hg, ?_⟩
  change c * g ∈ Subgroup.centralizer (ψ'.range : Set G)
  have hT : (Subgroup.centralizer ({c * g} : Set G)).comap ψ' = ⊤ := by
    rw [eq_top_iff, ← ggClosure_xm_simple_eq_top e6Data_valid (GaloisField 2 1)]
    rw [Subgroup.closure_le]
    rintro z ⟨i, t, hz⟩
    rcases hz with rfl | rfl
    · rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hpos i t).symm
    · rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hneg i t).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨u, rfl⟩ := hy
  have hu : ψ' u ∈ Subgroup.centralizer ({c * g} : Set G) := by
    have : u ∈ (Subgroup.centralizer ({c * g} : Set G)).comap ψ' := by
      rw [hT]
      trivial
    exact Subgroup.mem_comap.mp this
  exact (Subgroup.mem_centralizer_iff.mp hu (c * g) (Set.mem_singleton _)).symm

end Inner

end CFSG.StandardType
