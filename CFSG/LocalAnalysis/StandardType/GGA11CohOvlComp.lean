module

public import CFSG.LocalAnalysis.StandardType.GGA11CohDefs

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

private lemma a11oc_swap_lt3 {l m : Fin 4} (h : l ≠ m) : (Equiv.swap l 3 m).val < 3 := by
  fin_cases l <;> fin_cases m <;> simp_all <;> decide

private lemma a11oc_swapBlocks_apply_invol (l : Fin 4) (x : Fin 12) :
    swapBlocks l (swapBlocks l x) = x := by
  fin_cases l <;> fin_cases x <;> decide

private lemma a11oc_forw {l m : Fin 4} (hlm : l ≠ m) (a : Fin 12)
    (ha : blk a ≠ l) (ham : blk a ≠ m) :
    (swapBlocks l a).val < 9 ∧ blk (swapBlocks l a) ≠ Equiv.swap l 3 m := by
  fin_cases l <;> fin_cases m
  all_goals try (exfalso; exact hlm rfl)
  all_goals fin_cases a
  all_goals try (exfalso; exact ha rfl)
  all_goals try (exfalso; exact ham rfl)
  all_goals decide

private lemma a11oc_back {l m : Fin 4} (hlm : l ≠ m) (c : Fin 12)
    (hc : c.val < 9) (hcs : blk c ≠ Equiv.swap l 3 m) :
    blk (swapBlocks l c) ≠ l ∧ blk (swapBlocks l c) ≠ m := by
  fin_cases l <;> fin_cases m
  all_goals try (exfalso; exact hlm rfl)
  all_goals fin_cases c
  all_goals try (exfalso; revert hc; decide)
  all_goals try (exfalso; revert hcs; decide)
  all_goals decide

private lemma a11oc_map_centralizer_of_injective {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (hf : Function.Injective f) (t : G) :
    (Subgroup.centralizer ({t} : Set G)).map f =
      f.range ⊓ Subgroup.centralizer ({f t} : Set G') := by
  refine le_antisymm ?_ ?_
  · refine le_inf (Subgroup.map_le_range f _) ?_
    have h := Subgroup.map_centralizer_le_centralizer_image ({t} : Set G) f
    simpa using h
  · rintro x ⟨⟨y, rfl⟩, hx⟩
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    have hx' := (Subgroup.mem_centralizer_iff).mp hx
    exact (Subgroup.mem_centralizer_iff).mpr (fun s hs => by
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      apply hf
      rw [map_mul, map_mul]
      exact hx' (f t) (Set.mem_singleton (f t)))

private lemma a11oc_map_centralizer_conj {G : Type*} [Group G] (g t : G) :
    (Subgroup.centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
  rw [a11oc_map_centralizer_of_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective t]
  have htop : (MulAut.conj g).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective
  rw [htop]
  simp [MulAut.conj_apply]

private lemma a11oc_map_inf_of_injective {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (hf : Function.Injective f) (H K : Subgroup G) :
    (H ⊓ K).map f = H.map f ⊓ K.map f := by
  refine le_antisymm (le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)) ?_
  rintro x ⟨⟨h, hh, rfl⟩, ⟨k, hk, hkf⟩⟩
  refine Subgroup.mem_map.mpr ⟨h, ⟨hh, ?_⟩, rfl⟩
  have hkh : k = h := hf hkf
  rw [← hkh]
  exact hk

private lemma a11oc_isComponentOf_map_of_injective {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (hf : Function.Injective f) {L K : Subgroup G}
    (h : CFSG.Assembly.IsComponentOf L K) :
    CFSG.Assembly.IsComponentOf (L.map f) (K.map f) := by
  refine ⟨Subgroup.map_mono h.1, CFSG.Assembly.IsSubnormal.map f h.2.1, ?_⟩
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
    (Subgroup.equivMapOfInjective L f hf).symm h.2.2

private lemma a11oc_centralizer_pair {G : Type*} [Group G] (a b : G) :
    Subgroup.centralizer ({a, b} : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext x
  simp [Subgroup.mem_centralizer_iff, Subgroup.mem_inf]

theorem a11OvlCompInput_holds :
    A11WsubInput → ∀ (G : Type) [Group G] [Finite G] (φ₃ : SL 9 →* G) (f n : Fin 4 → G),
      A11GlueHyp φ₃ f n → ∀ l m : Fin 4, l ≠ m →
        IsComponentOf (Ovl φ₃ n l m) (Subgroup.centralizer ({f l, f m} : Set G)) ∧
          Subgroup.center ↥(Ovl φ₃ n l m) = ⊥ ∧ ∀ k : Fin 4, k ≠ l → k ≠ m → f k ∈ Ovl φ₃ n l m := by
  intro hW G _ _ φ₃ f n hGlue l m hlm
  obtain ⟨hφinj, hfT, hfcomm, hforder, hfcard, hn3, hnconj, hKcomp⟩ := hGlue
  set s4 : Fin 4 := Equiv.swap l 3 m with hs4def
  have hs4lt : s4.val < 3 := by rw [hs4def]; exact a11oc_swap_lt3 hlm
  set s3 : Fin 3 := ⟨s4.val, hs4lt⟩ with hs3def
  have hs3 : s3.castSucc = s4 := Fin.ext rfl
  have hs4inv : Equiv.swap l 3 s4 = m := by
    rw [hs4def]; exact Equiv.swap_apply_self l 3 m
  obtain ⟨hWcomp, hWcenter, hWtorus⟩ := hW s3
  have hfs : f s4 = φ₃ (T9 s3) := by rw [← hs3]; exact hfT s3
  have hnf : n l * f s4 * (n l)⁻¹ = f m := by rw [hnconj l s4, hs4inv]
  set ψ : SL 9 →* G := (MulAut.conj (n l)).toMonoidHom.comp φ₃ with hψdef
  have hψinj : Function.Injective ψ := by
    rw [hψdef]
    exact (MulAut.conj (n l)).injective.comp hφinj
  have hOvl : Ovl φ₃ n l m = (Wsub s3).map ψ := by
    let WGen : Set (SL 9) := {g | ∃ a b : Fin 12, a ≠ b ∧ a.val < 9 ∧ b.val < 9 ∧
      blk a ≠ s3.castSucc ∧ blk b ≠ s3.castSucc ∧ g = tv9 a b}
    let OvGen : Set G := {g | ∃ a b : Fin 12, a ≠ b ∧ blk a ≠ l ∧ blk b ≠ l ∧
      blk a ≠ m ∧ blk b ≠ m ∧ g = Xe φ₃ n l a b}
    have hWsub : Wsub s3 = Subgroup.closure WGen := rfl
    have hOvlGen : Ovl φ₃ n l m = Subgroup.closure OvGen := rfl
    have hset : ψ '' WGen = OvGen := by
      ext g
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨a, b, hab, ha9, hb9, hacs, hbcs, rfl⟩ := hw
        have hacs' : blk a ≠ s4 := by rw [← hs3]; exact hacs
        have hbcs' : blk b ≠ s4 := by rw [← hs3]; exact hbcs
        obtain ⟨hla, hlam⟩ := a11oc_back hlm a ha9 hacs'
        obtain ⟨hlb, hlbm⟩ := a11oc_back hlm b hb9 hbcs'
        refine ⟨swapBlocks l a, swapBlocks l b, ?_, hla, hlb, hlam, hlbm, ?_⟩
        · exact fun h => hab ((swapBlocks l).injective h)
        · rw [hψdef, MonoidHom.comp_apply]
          simp only [Xe, tvAt, a11oc_swapBlocks_apply_invol]
          rfl
      · intro hg
        obtain ⟨a, b, hab, hal, hbl, ham, hbm, hgXe⟩ := hg
        rw [hgXe]
        obtain ⟨ha9, hac⟩ := a11oc_forw hlm a hal ham
        obtain ⟨hb9, hbc⟩ := a11oc_forw hlm b hbl hbm
        refine ⟨tvAt l a b, ?_, ?_⟩
        · refine ⟨swapBlocks l a, swapBlocks l b, ?_, ha9, hb9, ?_, ?_, rfl⟩
          · exact fun h => hab ((swapBlocks l).injective h)
          · rw [hs3]; exact hac
          · rw [hs3]; exact hbc
        · rw [hψdef, MonoidHom.comp_apply]
          simp only [Xe]
          rfl
    rw [hOvlGen, hWsub, MonoidHom.map_closure, hset]
  have hKcomp' : CFSG.Assembly.IsComponentOf (φ₃.range.map (MulAut.conj (n l)).toMonoidHom)
      (Subgroup.centralizer ({f l} : Set G)) := by
    have hmap := a11oc_isComponentOf_map_of_injective (MulAut.conj (n l)).toMonoidHom
      (MulAut.conj (n l)).injective hKcomp
    rw [a11oc_map_centralizer_conj] at hmap
    rw [hnconj l 3, Equiv.swap_apply_right] at hmap
    exact hmap
  have hφWcomp : CFSG.Assembly.IsComponentOf ((Wsub s3).map φ₃)
      (φ₃.range ⊓ Subgroup.centralizer ({f s4} : Set G)) := by
    have hmap := a11oc_isComponentOf_map_of_injective φ₃ hφinj hWcomp
    rw [a11oc_map_centralizer_of_injective φ₃ hφinj (T9 s3)] at hmap
    rw [← hfs] at hmap
    exact hmap
  have hOvcomp : CFSG.Assembly.IsComponentOf (Ovl φ₃ n l m)
      ((φ₃.range.map (MulAut.conj (n l)).toMonoidHom) ⊓
        Subgroup.centralizer ({f m} : Set G)) := by
    have hmap := a11oc_isComponentOf_map_of_injective (MulAut.conj (n l)).toMonoidHom
      (MulAut.conj (n l)).injective hφWcomp
    rw [Subgroup.map_map] at hmap
    rw [← hψdef] at hmap
    rw [← hOvl] at hmap
    rw [a11oc_map_inf_of_injective (MulAut.conj (n l)).toMonoidHom
      (MulAut.conj (n l)).injective] at hmap
    rw [a11oc_map_centralizer_conj] at hmap
    rw [hnf] at hmap
    exact hmap
  have hKmid : CFSG.Assembly.IsSubnormal
      ((φ₃.range.map (MulAut.conj (n l)).toMonoidHom) ⊓
        Subgroup.centralizer ({f m} : Set G))
      (Subgroup.centralizer ({f l, f m} : Set G)) := by
    have h := hKcomp'.2.1.inf (Subgroup.centralizer ({f m} : Set G))
    rw [a11oc_centralizer_pair]
    exact h
  have hOvsub : CFSG.Assembly.IsSubnormal (Ovl φ₃ n l m)
      (Subgroup.centralizer ({f l, f m} : Set G)) :=
    hOvcomp.2.1.trans hKmid
  have hOvIsComp : CFSG.Assembly.IsComponentOf (Ovl φ₃ n l m)
      (Subgroup.centralizer ({f l, f m} : Set G)) :=
    ⟨hOvsub.le, hOvsub, hOvcomp.2.2⟩
  have hcenter : Subgroup.center ↥(Ovl φ₃ n l m) = ⊥ := by
    have he : ↥(Wsub s3) ≃* ↥(Ovl φ₃ n l m) :=
      (Subgroup.equivMapOfInjective (Wsub s3) ψ hψinj).trans
        (MulEquiv.subgroupCongr hOvl.symm)
    rw [← Subgroup.map_center_eq he, hWcenter, Subgroup.map_bot]
  have hmem : ∀ k : Fin 4, k ≠ l → k ≠ m → f k ∈ Ovl φ₃ n l m := by
    intro k hkl hkm
    set k4 : Fin 4 := Equiv.swap l 3 k with hk4def
    have hk4lt : k4.val < 3 := by rw [hk4def]; exact a11oc_swap_lt3 (Ne.symm hkl)
    set k3 : Fin 3 := ⟨k4.val, hk4lt⟩ with hk3def
    have hk3 : k3.castSucc = k4 := Fin.ext rfl
    have hk3_ne : k3 ≠ s3 := by
      intro h
      have hk4s4 : k4 = s4 := by
        rw [← hk3, ← hs3]
        exact congrArg Fin.castSucc h
      have hkm' : k = m := by
        have h' : Equiv.swap l 3 k = Equiv.swap l 3 m := by
          rw [← hk4def, ← hs4def]
          exact hk4s4
        have h'' := congrArg (Equiv.swap l 3) h'
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_self] at h''
      exact hkm hkm'
    have hT9 : T9 k3 ∈ Wsub s3 := hWtorus k3 hk3_ne
    have hswapk : Equiv.swap l 3 k4 = k := by
      rw [hk4def]
      exact Equiv.swap_apply_self l 3 k
    have hfk_eq : f k = n l * f k4 * (n l)⁻¹ := by
      rw [hnconj l k4, hswapk]
    have hfkT : f k4 = φ₃ (T9 k3) := by rw [← hk3]; exact hfT k3
    have hfk : f k = ψ (T9 k3) := by
      rw [hfk_eq, hfkT, hψdef, MonoidHom.comp_apply]
      rfl
    rw [hfk, hOvl]
    exact Subgroup.mem_map.mpr ⟨T9 k3, hT9, rfl⟩
  exact ⟨hOvIsComp, hcenter, hmem⟩

end CFSG.StandardType.A11

end
