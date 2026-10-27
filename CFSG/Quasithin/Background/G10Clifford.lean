module

public import CFSG.Quasithin.Background.G10Basic
public import CFSG.Quasithin.Background.G11Basic
public import CFSG.Quasithin.Background.G10Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace G108Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem L_le : L ≤ Γ := hyp.component.1

theorem H_le : normalClosure Γ L ≤ Γ := normalClosure_le hyp.L_le

theorem H_isometry : ∀ k ∈ normalClosure Γ L, ∀ v w, B (k v) (k w) = B v w :=
  fun _ hk => hyp.isometry _ (hyp.H_le hk)

theorem exists_ne_one_mem_L : ∃ l ∈ L, l ≠ 1 := by
  obtain ⟨x, -, l, hl, h⟩ := hyp.noncomm
  exact ⟨l, hl, fun h1 => h (by rw [h1, mul_one, one_mul])⟩

theorem fixedSpace_H : fixedSpace (normalClosure Γ L) = ⊥ := by
  have hinv : Invariant Γ (fixedSpace (normalClosure Γ L)) :=
    invariant_fixedSpace (normalClosure_normal Γ L)
  rcases hyp.irreducible.eq_bot_or_eq hinv le_top with h | h
  · exact h
  · exfalso
    obtain ⟨l, hl, hl1⟩ := hyp.exists_ne_one_mem_L
    exact hl1 (fixedSpace_eq_top_iff.1 h l (le_normalClosure Γ L hl))

theorem commSpace_H : commSpace (normalClosure Γ L) ⊤ = ⊤ := by
  have hinv : Invariant Γ (commSpace (normalClosure Γ L) ⊤) :=
    invariant_commSpace (normalClosure_normal Γ L) (invariant_top Γ)
  rcases hyp.irreducible.eq_bot_or_eq hinv le_top with h | h
  · exfalso
    have hfix : fixedSpace (normalClosure Γ L) = ⊤ := by
      rw [eq_top_iff]
      intro v _ k hk
      exact (commSpace_eq_bot_iff.1 h) k hk v Submodule.mem_top
    exact hyp.irreducible.ne_bot (hfix.symm.trans hyp.fixedSpace_H)
  · exact h

theorem iSup_conj {I : Submodule (ZMod 2) V} (hI : IsIrr (normalClosure Γ L) I) :
    (⨆ γ : Γ, conjSub (γ : GLV V) I) = ⊤ :=
  iSup_conjSub_eq_top hyp.irreducible hI.ne_bot

theorem exists_isIrr : ∃ I : Submodule (ZMod 2) V, IsIrr (normalClosure Γ L) I := by
  obtain ⟨J, -, hJ⟩ :=
    exists_isIrr_le (invariant_top (normalClosure Γ L)) hyp.irreducible.ne_bot
  exact ⟨J, hJ⟩

theorem sSup_irrPlus : sSup {I | IrrPlus (normalClosure Γ L) I} = ⊤ := by
  obtain ⟨I, hI⟩ := hyp.exists_isIrr
  rw [eq_top_iff, ← hyp.iSup_conj hI]
  refine iSup_le fun γ => le_sSup ?_
  exact (hI.conj_of_normal (normalClosure_normal Γ L) γ.2).irrPlus hyp.fixedSpace_H

theorem sSup_isIrr : sSup {J : Submodule (ZMod 2) V | IsIrr (normalClosure Γ L) J} = ⊤ := by
  rw [eq_top_iff, ← hyp.sSup_irrPlus]
  exact sSup_le_sSup fun I hI => IrrPlus.isIrr hyp.fixedSpace_H hI

theorem isotropic_or_nondegOn {I : Submodule (ZMod 2) V} (hI : IsIrr (normalClosure Γ L) I) :
    Isotropic B I ∨ NondegOn B I := by
  have hrefl : B.IsRefl := hyp.toG101Hyp.isRefl
  have hinv : Invariant (normalClosure Γ L) (I ⊓ B.orthogonal I) :=
    hI.1.inf (hI.1.orthogonal hyp.H_isometry)
  rcases hI.eq_bot_or_eq hinv (inf_le_left : I ⊓ B.orthogonal I ≤ I) with h | h
  · right
    intro u hu hw
    have hu' : u ∈ I ⊓ B.orthogonal I := by
      refine Submodule.mem_inf.2 ⟨hu, ?_⟩
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      exact hrefl _ _ (hw n hn)
    rw [h] at hu'
    exact (Submodule.mem_bot _).1 hu'
  · left
    intro u hu u' hu'
    have : u' ∈ I ⊓ B.orthogonal I := by
      rw [h]
      exact hu'
    exact (LinearMap.BilinForm.mem_orthogonal_iff.1 (Submodule.mem_inf.1 this).2) u hu

theorem isCompl_orthogonal {I : Submodule (ZMod 2) V} (hI : NondegOn B I) :
    IsCompl I (B.orthogonal I) := by
  have hrefl : B.IsRefl := hyp.toG101Hyp.isRefl
  refine LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl ?_
  have h1 : ∀ x : I, (∀ y : I, (B.restrict I) x y = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    exact hI x x.2 fun w hw => hx ⟨w, hw⟩
  refine ⟨fun x hx => h1 x hx, fun x hx => h1 x fun y => ?_⟩
  have := hx y
  exact hrefl _ _ this

theorem exists_dual {I : Submodule (ZMod 2) V} (hI : IsIrr (normalClosure Γ L) I)
    (hiso : Isotropic B I) : ∃ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J ∧
      IsDualOf (normalClosure Γ L) I J ∧ NondegOn B (I ⊔ J) := by
  have hrefl : B.IsRefl := hyp.toG101Hyp.isRefl
  have hnd : B.Nondegenerate := hyp.toG101Hyp.nondegenerate'
  set H := normalClosure Γ L with hH
  have hPinv : Invariant H (B.orthogonal I) := hI.1.orthogonal hyp.H_isometry
  have hIP : I ≤ B.orthogonal I := fun u hu => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact fun n hn => hiso n hn u hu
  have hPP : B.orthogonal (B.orthogonal I) = I :=
    LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl I
  obtain ⟨J, hJinv, hcompl⟩ := exists_invariant_compl hyp.sSup_isIrr hPinv
  have hdim1 : Module.finrank (ZMod 2) ↥(B.orthogonal I) =
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) ↥I :=
    LinearMap.BilinForm.finrank_orthogonal hnd I
  have hdim2 := Submodule.finrank_add_eq_of_isCompl hcompl
  have hdimI : Module.finrank (ZMod 2) ↥I ≤ Module.finrank (ZMod 2) V := Submodule.finrank_le I
  have hdimJ : Module.finrank (ZMod 2) ↥J = Module.finrank (ZMod 2) ↥I := by omega
  have hJirr : IsIrr H J := by
    refine ⟨hJinv, bot_lt_iff_ne_bot.2 ?_, fun J' hJ' _ hJ'J => ?_⟩
    · intro hJ0
      apply hI.ne_bot
      rw [hJ0] at hdimJ
      simpa using hdimJ.symm
    · have hR : Invariant H (I ⊓ B.orthogonal J') := hI.1.inf (hJ'.orthogonal hyp.H_isometry)
      rcases hI.eq_bot_or_eq hR inf_le_left with hR0 | hRI
      ·
        right
        have hQ : B.orthogonal (B.orthogonal I ⊔ J') = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
          have hxP : x ∈ B.orthogonal (B.orthogonal I) := by
            rw [LinearMap.BilinForm.mem_orthogonal_iff]
            exact fun n hn => hx n (Submodule.mem_sup_left hn)
          have hxJ' : x ∈ B.orthogonal J' := by
            rw [LinearMap.BilinForm.mem_orthogonal_iff]
            exact fun n hn => hx n (Submodule.mem_sup_right hn)
          rw [hPP] at hxP
          have : x ∈ I ⊓ B.orthogonal J' := ⟨hxP, hxJ'⟩
          rw [hR0] at this
          exact this
        have hQtop : B.orthogonal I ⊔ J' = ⊤ := by
          apply Submodule.eq_top_of_finrank_eq
          have h1 := LinearMap.BilinForm.finrank_orthogonal hnd (B.orthogonal I ⊔ J')
          rw [hQ, finrank_bot] at h1
          have h2 : Module.finrank (ZMod 2) ↥(B.orthogonal I ⊔ J') ≤ Module.finrank (ZMod 2) V :=
            Submodule.finrank_le _
          omega
        apply le_antisymm hJ'J
        intro x hx
        have hx' : x ∈ B.orthogonal I ⊔ J' := by rw [hQtop]; exact Submodule.mem_top
        obtain ⟨p, hp, j', hj', rfl⟩ := Submodule.mem_sup.1 hx'
        have hp' : p ∈ B.orthogonal I ⊓ J := ⟨hp, by
          have : p = (p + j') - j' := by abel
          rw [this]
          exact J.sub_mem hx (hJ'J hj')⟩
        have := hcompl.disjoint.le_bot hp'
        rw [Submodule.mem_bot] at this
        rw [this, zero_add]
        exact hj'
      ·
        left
        have hI' : I ≤ B.orthogonal J' := by rw [← hRI]; exact inf_le_right
        rw [eq_bot_iff]
        intro j hj
        have hjP : j ∈ B.orthogonal I := by
          rw [LinearMap.BilinForm.mem_orthogonal_iff]
          intro n hn
          have := (LinearMap.BilinForm.mem_orthogonal_iff.1 (hI' hn)) j hj
          exact hrefl _ _ this
        have := hcompl.disjoint.le_bot ⟨hjP, hJ'J hj⟩
        exact this
  refine ⟨J, hJirr.irrPlus hyp.fixedSpace_H, ?_, ?_⟩
  ·
    refine ⟨LinearMap.domRestrict₁₂ B J I, fun j hj => ?_, fun i hi => ?_, ?_⟩
    · have hjP : (j : V) ∈ B.orthogonal I := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro n hn
        exact hrefl _ _ (hj ⟨n, hn⟩)
      have := hcompl.disjoint.le_bot ⟨hjP, j.2⟩
      exact Subtype.ext this
    · apply Subtype.ext
      apply hyp.nondegenerate
      intro v
      have hv : v ∈ B.orthogonal I ⊔ J := by
        rw [codisjoint_iff.1 hcompl.codisjoint]
        exact Submodule.mem_top
      obtain ⟨p, hp, j₀, hj₀, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add]
      have h1 : B (i : V) p = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hp) i i.2
      have h2 : B (i : V) j₀ = 0 := hrefl _ _ (hi ⟨j₀, hj₀⟩)
      rw [h1, h2, add_zero]
    · intro k hk j j' i i' hj hi
      have : B (j' : V) (i' : V) = B (j : V) (i : V) := by
        rw [← hj, ← hi]
        exact hyp.H_isometry k hk _ _
      exact this
  ·
    intro x hx hx0
    obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.1 hx
    have hjP : j ∈ B.orthogonal I := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have h1 := hx0 n (Submodule.mem_sup_left hn)
      rw [map_add, LinearMap.add_apply, hiso i hi n hn, zero_add] at h1
      exact hrefl _ _ h1
    have hj0 : j = 0 := by
      have := hcompl.disjoint.le_bot ⟨hjP, hj⟩
      simpa using this
    subst hj0
    rw [add_zero]
    apply hyp.nondegenerate
    intro v
    have hv : v ∈ B.orthogonal I ⊔ J := by
      rw [codisjoint_iff.1 hcompl.codisjoint]
      exact Submodule.mem_top
    obtain ⟨p, hp, j₀, hj₀, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    have h1 : B i p = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hp) i hi
    have h2 : B i j₀ = 0 := by
      have := hx0 j₀ (Submodule.mem_sup_right hj₀)
      simpa using this
    rw [h1, h2, add_zero]

theorem two_lt_finrank {I : Submodule (ZMod 2) V} (hI : IsIrr (normalClosure Γ L) I) :
    2 < Module.finrank (ZMod 2) I := by
  by_contra hle
  have hle' : Module.finrank (ZMod 2) I ≤ 2 := not_lt.1 hle
  have hperf : Group.IsPerfect ↥L := ⟨hyp.component.2.2.1⟩
  have hL : ∀ γ ∈ Γ, ∀ l ∈ L, ∀ u ∈ conjSub γ I, l u = u := by
    intro γ hγ
    have hJ : IsIrr (normalClosure Γ L) (conjSub γ I) :=
      hI.conj_of_normal (normalClosure_normal Γ L) hγ
    have hfin : Module.finrank (ZMod 2) ↥(conjSub γ I) ≤ 2 := by
      rw [finrank_conjSub]
      exact hle'
    have hLinv : Invariant L (conjSub γ I) := hJ.1.mono (le_normalClosure Γ L)
    have hsolv := isSolvable_linearEquiv_of_finrank_le_two (conjSub γ I) hfin
    let φ := restrictHom L (conjSub γ I) hLinv
    have hsub : Subsingleton φ.range := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
      exact Group.IsPerfect.not_isSolvable (G := φ.range) inferInstance
    intro l hl u hu
    have h1 : φ ⟨l, hl⟩ = 1 := by
      have := Subsingleton.elim (⟨φ ⟨l, hl⟩, ⟨_, rfl⟩⟩ : φ.range) ⟨1, φ.range.one_mem⟩
      exact congrArg Subtype.val this
    exact (restrictHom_eq_one_iff.1 h1) u hu
  have hfix : fixedSpace L = ⊤ := by
    rw [eq_top_iff, ← hyp.iSup_conj hI]
    refine iSup_le fun γ u hu l hl => hL γ γ.2 l hl u hu
  obtain ⟨l, hl, hl1⟩ := hyp.exists_ne_one_mem_L
  exact hl1 (fixedSpace_eq_top_iff.1 hfix l hl)

theorem g10_7 : G1007Concl B Γ L := by
  refine ⟨hyp.fixedSpace_H, hyp.commSpace_H, hyp.sSup_irrPlus, fun I hI => ?_⟩
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  refine ⟨hirr, fun γ hγ => hirr.conj_eq_or_inf_eq_bot (normalClosure_normal Γ L) hγ,
    hyp.isotropic_or_nondegOn hirr, fun hnd => hyp.isCompl_orthogonal hnd,
    fun hiso => hyp.exists_dual hirr hiso, hyp.two_lt_finrank hirr⟩

end G108Hyp

theorem g10_7 : G1007Stmt := fun _ _ _ _ _ _ _ _ _ _ _ hyp => hyp.g10_7

end G11

end CFSG.Quasithin
