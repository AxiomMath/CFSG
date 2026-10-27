module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofChainFin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

open CFSG.StandardType

namespace CFSG.StandardType.TypeAReflOver

theorem map_swap_eq_swap_of_embedding {β : Type*} [DecidableEq β] {n : ℕ}
    {g : Equiv.Perm (Fin (n + 1)) → Equiv.Perm β} {ι : Fin (n + 1) → β}
    (hι : Function.Injective ι) (h₁ : ∀ σ a, g σ (ι a) = ι (σ a))
    (h₂ : ∀ σ w, w ∉ Set.range ι → g σ w = w) (a b : Fin (n + 1)) :
    g (Equiv.swap a b) = Equiv.swap (ι a) (ι b) := by
  classical
  ext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨c, rfl⟩ := hx
    rw [h₁, Function.Injective.map_swap hι a b c]
  · have hxa : x ≠ ι a := fun h => hx ⟨a, h.symm⟩
    have hxb : x ≠ ι b := fun h => hx ⟨b, h.symm⟩
    rw [h₂ _ _ hx, Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem exists_embedding_of_isSwap {β : Type*} [DecidableEq β] [Fintype β] {n : ℕ}
    (hn : 2 ≤ n) (f : Equiv.Perm (Fin (n + 1)) →* Equiv.Perm β)
    (hf : Function.Injective f)
    (hsw : ∀ a b : Fin (n + 1), a ≠ b → (f (Equiv.swap a b)).IsSwap) :
    ∃ ι : Fin (n + 1) → β, Function.Injective ι ∧ (∀ σ a, f σ (ι a) = ι (σ a)) ∧
      ∀ σ w, w ∉ Set.range ι → f σ w = w := by
  let s : ℕ → Equiv.Perm β :=
    fun c => f (Equiv.swap (finTrunc n c) (finTrunc n (c + 1)))
  have hne_fin : ∀ c d : ℕ, c ≤ n → d ≤ n → c ≠ d → finTrunc n c ≠ finTrunc n d := by
    intro c d hc hd hcd h
    exact hcd (by
      have := congrArg Fin.val h
      rwa [finTrunc_val_of_le hc, finTrunc_val_of_le hd] at this)
  have hsw' : ∀ c, c < n → (s c).IsSwap := by
    intro c hc
    simpa only [s] using
      hsw (finTrunc n c) (finTrunc n (c + 1))
        (hne_fin c (c + 1) (by omega) (by omega) (by omega))
  have hne' : ∀ c d, c < d → d < n → s c ≠ s d := by
    intro c d hcd hdn heq
    have h1 : Equiv.swap (finTrunc n c) (finTrunc n (c + 1))
        = Equiv.swap (finTrunc n d) (finTrunc n (d + 1)) := by
      apply hf
      simpa only [s] using heq
    have h2 := congrArg (fun e : Equiv.Perm (Fin (n + 1)) => e (finTrunc n c)) h1
    rw [Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (hne_fin c d (by omega) (by omega) (by omega))
          (hne_fin c (d + 1) (by omega) (by omega) (by omega))] at h2
    have h3 := congrArg Fin.val h2
    rw [finTrunc_val_of_le (n := n) (c := c + 1) (by omega),
        finTrunc_val_of_le (n := n) (c := c) (by omega)] at h3
    omega
  have hbr' : ∀ c, c + 1 < n → (s c * s (c + 1)) ^ 3 = 1 := by
    intro c hc
    have hcyc : (Equiv.swap (finTrunc n c) (finTrunc n (c + 1))
        * Equiv.swap (finTrunc n (c + 1)) (finTrunc n (c + 2))).IsThreeCycle := by
      rw [Equiv.swap_comm (finTrunc n c) (finTrunc n (c + 1))]
      exact Equiv.Perm.isThreeCycle_swap_mul_swap_same
        (hne_fin (c + 1) c (by omega) (by omega) (by omega))
        (hne_fin (c + 1) (c + 2) (by omega) (by omega) (by omega))
        (hne_fin c (c + 2) (by omega) (by omega) (by omega))
    have hcube : (Equiv.swap (finTrunc n c) (finTrunc n (c + 1))
        * Equiv.swap (finTrunc n (c + 1)) (finTrunc n (c + 2))) ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hcyc.orderOf]
    have hmap : s c * s (c + 1)
        = f (Equiv.swap (finTrunc n c) (finTrunc n (c + 1))
            * Equiv.swap (finTrunc n (c + 1)) (finTrunc n (c + 2))) := by
      change f (Equiv.swap (finTrunc n c) (finTrunc n (c + 1)))
          * f (Equiv.swap (finTrunc n (c + 1)) (finTrunc n (c + 2)))
        = f (Equiv.swap (finTrunc n c) (finTrunc n (c + 1))
            * Equiv.swap (finTrunc n (c + 1)) (finTrunc n (c + 2)))
      rw [map_mul]
    rw [hmap, ← map_pow, hcube, map_one]
  have hcomm' : ∀ c d, c + 2 ≤ d → d < n → s c * s d = s d * s c := by
    intro c d hcd hdn
    have hnd : [finTrunc n c, finTrunc n (c + 1), finTrunc n d,
        finTrunc n (d + 1)].Nodup := by
      have h1 : finTrunc n c ≠ finTrunc n (c + 1) :=
        hne_fin c (c + 1) (by omega) (by omega) (by omega)
      have h2 : finTrunc n c ≠ finTrunc n d :=
        hne_fin c d (by omega) (by omega) (by omega)
      have h3 : finTrunc n c ≠ finTrunc n (d + 1) :=
        hne_fin c (d + 1) (by omega) (by omega) (by omega)
      have h4 : finTrunc n (c + 1) ≠ finTrunc n d :=
        hne_fin (c + 1) d (by omega) (by omega) (by omega)
      have h5 : finTrunc n (c + 1) ≠ finTrunc n (d + 1) :=
        hne_fin (c + 1) (d + 1) (by omega) (by omega) (by omega)
      have h6 : finTrunc n d ≠ finTrunc n (d + 1) :=
        hne_fin d (d + 1) (by omega) (by omega) (by omega)
      simpa [h1, h2, h3, h4, h5, h6]
    have hdisj : (Equiv.swap (finTrunc n c) (finTrunc n (c + 1))).Disjoint
        (Equiv.swap (finTrunc n d) (finTrunc n (d + 1))) :=
      Equiv.Perm.disjoint_swap_swap hnd
    have hcommFin : Equiv.swap (finTrunc n c) (finTrunc n (c + 1))
        * Equiv.swap (finTrunc n d) (finTrunc n (d + 1))
        = Equiv.swap (finTrunc n d) (finTrunc n (d + 1))
          * Equiv.swap (finTrunc n c) (finTrunc n (c + 1)) := hdisj.commute
    have hmap : s c * s d
        = f (Equiv.swap (finTrunc n c) (finTrunc n (c + 1))
            * Equiv.swap (finTrunc n d) (finTrunc n (d + 1))) := by
      change f (Equiv.swap (finTrunc n c) (finTrunc n (c + 1)))
          * f (Equiv.swap (finTrunc n d) (finTrunc n (d + 1)))
        = f (Equiv.swap (finTrunc n c) (finTrunc n (c + 1))
            * Equiv.swap (finTrunc n d) (finTrunc n (d + 1)))
      rw [map_mul]
    rw [hmap, hcommFin, map_mul]
  obtain ⟨w, hw, hsw_rep⟩ := chain_labels s n hn hsw' hne' hbr' hcomm'
  let ι : Fin (n + 1) → β := fun a => w a.val
  have hι : Function.Injective ι := by
    intro a b hab
    exact Fin.ext (hw a.val b.val (by omega) (by omega) hab)
  let ιe : Fin (n + 1) ↪ β := ⟨ι, hι⟩
  let g : Equiv.Perm (Fin (n + 1)) →* Equiv.Perm β := Equiv.Perm.viaEmbeddingHom ιe
  have hg₁ : ∀ σ a, g σ (ι a) = ι (σ a) := by
    intro σ a
    rw [show g σ = σ.viaEmbedding ιe from Equiv.Perm.viaEmbeddingHom_apply σ ιe]
    change (σ.viaEmbedding ιe) (ιe a) = ιe (σ a)
    exact Equiv.Perm.viaEmbedding_apply σ ιe a
  have hg₂ : ∀ σ x, x ∉ Set.range ι → g σ x = x := by
    intro σ x hx
    rw [show g σ = σ.viaEmbedding ιe from Equiv.Perm.viaEmbeddingHom_apply σ ιe]
    change (σ.viaEmbedding ιe) x = x
    exact Equiv.Perm.viaEmbedding_apply_of_notMem σ ιe x hx
  have hfg : f = g := by
    refine MonoidHom.eq_of_eqOn_denseM (Equiv.Perm.mclosure_swap_castSucc_succ n) ?_
    rintro σ ⟨i, rfl⟩
    have hfi : f (Equiv.swap i.castSucc i.succ)
        = Equiv.swap (ι i.castSucc) (ι i.succ) := by
      have hrep : f (Equiv.swap (finTrunc n i.val) (finTrunc n (i.val + 1)))
          = Equiv.swap (w i.val) (w (i.val + 1)) := by
        simpa only [s] using hsw_rep i.val i.isLt
      have hc : (i.castSucc : Fin (n + 1)) = finTrunc n i.val := by
        apply Fin.ext
        rw [Fin.val_castSucc, finTrunc_val_of_le (by omega)]
      have hs : (i.succ : Fin (n + 1)) = finTrunc n (i.val + 1) := by
        apply Fin.ext
        rw [Fin.val_succ, finTrunc_val_of_le (by omega)]
      calc
        f (Equiv.swap i.castSucc i.succ)
            = f (Equiv.swap (finTrunc n i.val) (finTrunc n (i.val + 1))) := by
              rw [hc, hs]
        _ = Equiv.swap (w i.val) (w (i.val + 1)) := hrep
        _ = Equiv.swap (ι i.castSucc) (ι i.succ) := by
              simp only [ι, Fin.val_castSucc, Fin.val_succ]
    have hgi : g (Equiv.swap i.castSucc i.succ)
        = Equiv.swap (ι i.castSucc) (ι i.succ) :=
      map_swap_eq_swap_of_embedding (g := ⇑g) hι hg₁ hg₂ i.castSucc i.succ
    rw [hfi, hgi]
  refine ⟨ι, hι, ?_, ?_⟩
  · intro σ a
    rw [hfg]
    exact hg₁ σ a
  · intro σ x hx
    rw [hfg]
    exact hg₂ σ x hx

end CFSG.StandardType.TypeAReflOver
