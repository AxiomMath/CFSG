module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseM17Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModF2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43

open Equiv CFSG.Quasithin.F53Mod

section Generic

variable (M W : Model 5) (F : Subgroup W.W) (φ : M.W ≃* ↥F)

@[expose] def m17Cocycle (hA : ∀ σ ∈ alternatingGroup (Fin 5), ∀ w : W.W, W.act σ w * w⁻¹ ∈ F)
    (w : W.W) (g : alternatingGroup (Fin 5)) : M.W :=
  φ.symm ⟨W.act g w * w⁻¹, hA g g.2 w⟩

variable {M W F φ}

theorem m17_coe_cocycle {hA : ∀ σ ∈ alternatingGroup (Fin 5), ∀ w : W.W, W.act σ w * w⁻¹ ∈ F}
    (w : W.W) (g : alternatingGroup (Fin 5)) :
    ((φ (m17Cocycle M W F φ hA w g) : ↥F) : W.W) = W.act g w * w⁻¹ := by
  simp [m17Cocycle]

theorem m17_cocycle_mul
    (hφ : ∀ (σ : Perm (Fin 5)) (u : M.W),
      ((φ (M.act σ u) : ↥F) : W.W) = W.act σ ((φ u : ↥F) : W.W))
    {hA : ∀ σ ∈ alternatingGroup (Fin 5), ∀ w : W.W, W.act σ w * w⁻¹ ∈ F}
    (w : W.W) (g h : alternatingGroup (Fin 5)) :
    m17Cocycle M W F φ hA w (g * h) =
      m17Cocycle M W F φ hA w g * M.act (g : Perm (Fin 5)) (m17Cocycle M W F φ hA w h) := by
  apply φ.injective
  apply Subtype.ext
  rw [map_mul, Subgroup.coe_mul, hφ, m17_coe_cocycle, m17_coe_cocycle, m17_coe_cocycle]
  simp only [Subgroup.coe_mul, map_mul, MulAut.mul_apply, map_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem m17_mem_of_principal
    (hφ : ∀ (σ : Perm (Fin 5)) (u : M.W),
      ((φ (M.act σ u) : ↥F) : W.W) = W.act σ ((φ u : ↥F) : W.W))
    {hA : ∀ σ ∈ alternatingGroup (Fin 5), ∀ w : W.W, W.act σ w * w⁻¹ ∈ F}
    (hC : ∀ w : W.W, (∀ σ ∈ alternatingGroup (Fin 5), W.act σ w = w) → w = 1)
    (w : W.W) (u : M.W)
    (hu : ∀ g : alternatingGroup (Fin 5),
      m17Cocycle M W F φ hA w g = M.act (g : Perm (Fin 5)) u * u⁻¹) :
    w ∈ F := by
  set v : W.W := ((φ u : ↥F) : W.W) with hv
  have h1 : w * v⁻¹ = 1 := by
    apply hC
    intro σ hσ
    have e := congrArg (fun z : M.W => ((φ z : ↥F) : W.W)) (hu ⟨σ, hσ⟩)
    simp only [m17_coe_cocycle, map_mul, Subgroup.coe_mul, hφ, map_inv, Subgroup.coe_inv] at e
    rw [map_mul, map_inv]
    have e' : W.act σ w = W.act σ v * v⁻¹ * w := by
      rw [← e]; simp [mul_comm]
    rw [e']
    simp [mul_comm, mul_assoc]
  have : w = v := by rwa [mul_inv_eq_one] at h1
  rw [this]
  exact (φ u).2

end Generic

theorem m17_orth : M17Orth := by
  intro W F φ hφ hA hC
  refine eq_top_iff.mpr fun w _ => ?_
  obtain ⟨u, hu⟩ := h1_alt5_orth (m17Cocycle orth W F φ hA w)
    (fun g h => m17_cocycle_mul hφ w g h)
  exact m17_mem_of_principal hφ hC w u hu

section NatPart

variable {W : Model 5} {F : Subgroup W.W} {φ : nat.W ≃* ↥F}
  {hA : ∀ σ ∈ alternatingGroup (Fin 5), ∀ w : W.W, W.act σ w * w⁻¹ ∈ F}

theorem m17_cocycle_mul_w (w w' : W.W) (g : alternatingGroup (Fin 5)) :
    m17Cocycle nat W F φ hA (w * w') g =
      m17Cocycle nat W F φ hA w g * m17Cocycle nat W F φ hA w' g := by
  apply φ.injective
  apply Subtype.ext
  rw [map_mul, Subgroup.coe_mul, m17_coe_cocycle, m17_coe_cocycle, m17_coe_cocycle]
  simp only [map_mul, mul_inv_rev]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem m17_equivariant
    (hφ : ∀ (σ : Perm (Fin 5)) (u : nat.W),
      ((φ (nat.act σ u) : ↥F) : W.W) = W.act σ ((φ u : ↥F) : W.W))
    {w : W.W} (hw : ∀ σ ∈ S5That, W.act σ w = w) {t : Perm (Fin 5)} (ht : t ∈ S5That)
    (g h : alternatingGroup (Fin 5)) (hgh : (h : Perm (Fin 5)) = t * g * t⁻¹) :
    m17Cocycle nat W F φ hA w h = nat.act t (m17Cocycle nat W F φ hA w g) := by
  apply φ.injective
  apply Subtype.ext
  rw [m17_coe_cocycle, hφ, m17_coe_cocycle]
  have h1 : W.act t⁻¹ w = w := hw _ (inv_mem ht)
  have h2 : W.act t w = w := hw _ ht
  have h3 : W.act (h : Perm (Fin 5)) w = W.act t (W.act g w) := by
    rw [hgh, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, h1]
  rw [h3, map_mul, map_inv, h2]

theorem m17_mem_of_cob
    (hφ : ∀ (σ : Perm (Fin 5)) (u : nat.W),
      ((φ (nat.act σ u) : ↥F) : W.W) = W.act σ ((φ u : ↥F) : W.W))
    (hC : ∀ w : W.W, (∀ σ ∈ alternatingGroup (Fin 5), W.act σ w = w) → w = 1) (w : W.W)
    (h : m17Cob (m17Cocycle nat W F φ hA w m17A) (m17Cocycle nat W F φ hA w m17B)) :
    w ∈ F := by
  obtain ⟨u, hu1, hu2⟩ := h
  have hcoc : ∀ g h, m17Cocycle nat W F φ hA w (g * h) =
      m17Cocycle nat W F φ hA w g * m17act g (m17Cocycle nat W F φ hA w h) :=
    fun g h => m17_cocycle_mul hφ w g h
  exact m17_mem_of_principal hφ hC w u (crossed_principal_of_closure m17act hcoc {m17A, m17B}
    m17_closure u (by rintro s (rfl | rfl); exacts [hu1.symm, hu2.symm]))

theorem m17_swap02_mem : swap (0 : Fin 5) 2 ∈ S5That :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem m17_swap13_mem : swap (1 : Fin 5) 3 ∈ S5That :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem m17_data
    (hφ : ∀ (σ : Perm (Fin 5)) (u : nat.W),
      ((φ (nat.act σ u) : ↥F) : W.W) = W.act σ ((φ u : ↥F) : W.W))
    {w : W.W} (hw : ∀ σ ∈ S5That, W.act σ w = w) :
    (∀ l ∈ m17rels, wordV m17act m17A m17B (m17Cocycle nat W F φ hA w m17A)
      (m17Cocycle nat W F φ hA w m17B) l = 1) ∧
    m17Eqv (m17Cocycle nat W F φ hA w m17A) (m17Cocycle nat W F φ hA w m17B) := by
  have hcoc : ∀ g h, m17Cocycle nat W F φ hA w (g * h) =
      m17Cocycle nat W F φ hA w g * m17act g (m17Cocycle nat W F φ hA w h) :=
    fun g h => m17_cocycle_mul hφ w g h
  have key : ∀ (l : List Bool) (t : Perm (Fin 5)) (g : alternatingGroup (Fin 5)),
      t ∈ S5That → ((wordG m17A m17B l : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
        t * g * t⁻¹ → wordV m17act m17A m17B (m17Cocycle nat W F φ hA w m17A)
          (m17Cocycle nat W F φ hA w m17B) l = nat.act t (m17Cocycle nat W F φ hA w g) :=
    fun l t g ht hl => by
      rw [← crossed_word m17act hcoc, m17_equivariant hφ hw ht g _ hl]
  refine ⟨fun l hl => crossed_relator m17act hcoc m17A m17B l (m17rels_one l hl), ?_⟩
  exact ⟨key _ _ m17A m17_swap02_mem m17_conj_a.1, key _ _ m17B m17_swap02_mem m17_conj_b.1,
    key _ _ m17A m17_swap13_mem m17_conj_a.2, key _ _ m17B m17_swap13_mem m17_conj_b.2⟩

include hA in
theorem m17_key
    (hφ : ∀ (σ : Perm (Fin 5)) (u : nat.W),
      ((φ (nat.act σ u) : ↥F) : W.W) = W.act σ ((φ u : ↥F) : W.W))
    (hC : ∀ w : W.W, (∀ σ ∈ alternatingGroup (Fin 5), W.act σ w = w) → w = 1)
    {B : Subgroup W.W} (hB : ∀ σ ∈ S5That, ∀ b ∈ B, W.act σ b = b) {b b' : W.W}
    (hb : b ∈ B) (hb' : b' ∈ B) (nb : b ∉ F) (nb' : b' ∉ F) : b * b' ∈ F := by
  obtain ⟨r1, e1⟩ := m17_data (hA := hA) hφ (w := b) fun σ hσ => hB σ hσ b hb
  obtain ⟨r2, e2⟩ := m17_data (hA := hA) hφ (w := b') fun σ hσ => hB σ hσ b' hb'
  apply m17_mem_of_cob hφ hC
  rw [m17_cocycle_mul_w, m17_cocycle_mul_w]
  exact m17_check _ _ r1 e1 _ _ r2 e2 (fun h => nb (m17_mem_of_cob hφ hC b h))
    (fun h => nb' (m17_mem_of_cob hφ hC b' h))

theorem m17_index_le {W : Type*} [CommGroup W] (F B : Subgroup W)
    (key : ∀ b b' : W, b ∈ B → b' ∈ B → b ∉ F → b' ∉ F → b * b' ∈ F) :
    F.relIndex B ≤ 2 ∧ (B ⊔ F = ⊤ → F.relIndex ⊤ ≤ 2) := by
  by_cases hall : ∀ b ∈ B, b ∈ F
  · have hBF : B ≤ F := hall
    refine ⟨by rw [Subgroup.relIndex_eq_one.mpr hBF]; norm_num, fun h => ?_⟩
    rw [sup_eq_right.mpr hBF] at h
    rw [h, Subgroup.relIndex_top_right, Subgroup.index_top]
    norm_num
  · push Not at hall
    obtain ⟨b, hb, nb⟩ := hall
    refine ⟨?_, fun h => ?_⟩
    · have : F.relIndex B = 2 := by
        rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
        refine ⟨⟨b, hb⟩, fun c => ?_⟩
        simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
        by_cases hc : (c : W) ∈ F
        · exact Or.inr ⟨hc, fun h => nb (by simpa using F.mul_mem (F.inv_mem hc) h)⟩
        · exact Or.inl ⟨key _ _ c.2 hb hc nb, hc⟩
      omega
    · have : F.relIndex ⊤ = 2 := by
        rw [Subgroup.relIndex_top_right, Subgroup.index_eq_two_iff]
        refine ⟨b, fun c => ?_⟩
        have hc : c ∈ B ⊔ F := by rw [h]; trivial
        obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hc
        by_cases hyF : y ∈ F
        · exact Or.inr ⟨F.mul_mem hyF hz, fun h =>
            nb ((F.mul_mem_cancel_left (F.mul_mem hyF hz)).mp h)⟩
        · refine Or.inl ⟨?_, fun h => hyF ((F.mul_mem_cancel_right hz).mp h)⟩
          rw [mul_right_comm]
          exact F.mul_mem (key _ _ hy hb hyF nb) hz
      omega

end NatPart

theorem m17_nat : M17Nat := by
  intro W F φ hφ hA hC B hB hBF
  have key : ∀ b b' : W.W, b ∈ B → b' ∈ B → b ∉ F → b' ∉ F → b * b' ∈ F :=
    fun b b' hb hb' nb nb' => m17_key (hA := hA) hφ hC hB hb hb' nb nb'
  obtain ⟨h1, h2⟩ := m17_index_le F B key
  have hfix : Nat.card ↥(B ⊓ F) ≤ 2 := by
    have hprof := profile_nat.2.2.1
    unfold profile at hprof
    simp only [Prod.mk.injEq] at hprof
    rw [← hprof.2.1]
    refine Nat.card_le_card_of_injective
      (fun b : ↥(B ⊓ F) => (⟨φ.symm ⟨b, b.2.2⟩, fun t ht => ?_⟩ : ↥(fixW nat S5That))) ?_
    · apply φ.injective
      apply Subtype.ext
      rw [hφ]
      simp only [MulEquiv.apply_symm_apply]
      exact hB t ht b b.2.1
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (by simpa using this)
  refine ⟨h2 hBF, ?_, hfix⟩
  calc Nat.card B = F.relIndex B * Nat.card ↥(F ⊓ B) := (Subgroup.relIndex_mul_card F B).symm
    _ ≤ 2 * 2 := by
      rw [inf_comm]
      exact Nat.mul_le_mul h1 hfix

end CFSG.Quasithin.F53.Stellmacher.S43
