module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148NonSplitA
import CFSG.LocalAnalysis.UniquenessCase.UC22K148CompDich
import CFSG.LocalAnalysis.UniquenessCase.UC22K148S5Br
import CFSG.LocalAnalysis.UniquenessCase.UC22K148LemFP
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Split
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusionGL
import CFSG.RankThree.FFModules.FixSubConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem not_isComponentOf_sup_zpowers
    [Finite G] [Finite V]
    (hρ : Function.Injective ρ) (hH : hP ρ = ⊤)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hinner : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      ¬ ∀ g : G, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u)
    {N : Subgroup G} {a : G} (hN : N.Normal) (hcod : commOn ρ N ⊤ ⊔ fixSub ρ N = ⊤)
    (hsup : N ⊔ (cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a) = ⊤) {m : ℕ}
    {Hs : Fin m → Subgroup ↥(cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a)}
    (hD : IsInternalDirect ⊤ Hs) (i : Fin m) : ¬ IsComponentOf (Hs i) ⊤ := by
  intro hL
  have hK : (cenOn ρ ⊤ (commOn ρ N ⊤)).Normal := cenOn_commOn_normal hN
  have hLc := isComponentOf_map_subtype_sup_zpowers hK hL
  have hLK := map_subtype_sup_zpowers_le hK hL
  set L := (Hs i).map (cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a).subtype
  have hLE : commOn ρ L ⊤ ≤ fixSub ρ N := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, hl, v, -, rfl⟩
    have hv : v ∈ commOn ρ N ⊤ ⊔ fixSub ρ N := by
      rw [hcod]
      exact Submodule.mem_top
    obtain ⟨x, hx, e, he, rfl⟩ := Submodule.mem_sup.1 hv
    have e' : ρ l (x + e) - (x + e) = ρ l e - e := by
      rw [map_add, (hLK hl).2 x hx]
      abel
    rw [e']
    exact sub_mem (rep_apply_mem_fixSub_of_normal ρ hN l he) he
  rcases component_dichotomy hρ hH hLc (hshape L hLc) with h | ⟨-, b, hb2, hbN, hbL, hS5⟩
  · exact hinner L hLc h.1
  have hHn : (Hs i).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hD.1]
    refine iSup_le fun j => ?_
    by_cases hj : j = i
    · rw [hj]
      exact Subgroup.le_normalizer
    · refine le_trans (fun y hy => ?_) (Subgroup.centralizer_le_normalizer _)
      exact Subgroup.mem_centralizer_iff.2 fun x hx => hD.2.1 i j (Ne.symm hj) x hx y hy
  have htop : Hs i ⊔ ⨆ j ∈ {j | j ≠ i}, Hs j = ⊤ := by
    rw [eq_top_iff, ← hD.1]
    refine iSup_le fun j => ?_
    by_cases hj : j = i
    · rw [hj]
      exact le_sup_left
    · exact le_sup_of_le_right
        (le_iSup₂_of_le (f := fun j (_ : j ∈ {j | j ≠ i}) => Hs j) j hj le_rfl)
  have hR : (⨆ j ∈ {j | j ≠ i}, Hs j) ≤ Subgroup.centralizer (Hs i : Set _) :=
    iSup₂_le fun j hj y hy => Subgroup.mem_centralizer_iff.2 fun x hx =>
      hD.2.1 i j (Ne.symm (show j ≠ i from hj)) x hx y hy
  refine hinner L hLc fun g => ?_
  haveI := hN
  have hg : g ∈ N ⊔ (cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a) := by
    rw [hsup]
    exact Subgroup.mem_top g
  obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  haveI := hHn
  have hk' : (⟨k, hk⟩ : ↥(cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a)) ∈
      Hs i ⊔ ⨆ j ∈ {j | j ≠ i}, Hs j := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hk'
  have hzL : ∀ u ∈ commOn ρ L ⊤, ρ (z : G) u = u :=
    apply_eq_self_of_commute_of_secNatS5 hb2 hbN hbL hS5 fun l hl => by
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hl
      exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (hR hz) x hx)).symm
  have hyL : (y : G) ∈ L := Subgroup.mem_map_of_mem _ hy
  refine ⟨(y : G), hyL, fun u hu => ?_⟩
  have hk2 : k = (y : G) * (z : G) := (congrArg Subtype.val hyz).symm
  have hyu : ρ (y : G) u ∈ commOn ρ L ⊤ :=
    (invariant_commOn_top (A := ⊥) bot_le).1 _ hyL u hu
  rw [glRep_mul_apply, hk2, glRep_mul_apply, hzL u hu]
  exact mem_fixSub.1 (hLE hyu) n hn

theorem false_of_card_fixSub_subRep_le [Finite G] [Finite V] (hH : hP ρ = ⊤) {N : Subgroup G}
    {a : G} (hN : N.Normal) (hW : ∀ g : G, ∀ w ∈ fixSub ρ N, ρ g w ∈ fixSub ρ N)
    (hcompl : IsCompl (commOn ρ N ⊤) (fixSub ρ N)) (ha2 : a * a = 1)
    (hfa : ∀ n ∈ N, (∀ x ∈ commOn ρ N ⊤, ρ n x = x) → n = 1)
    (hact : ∀ g : G, ∃ h ∈ N ⊔ Subgroup.zpowers a, ∀ x ∈ commOn ρ N ⊤, ρ g x = ρ h x)
    (hout : ∀ n ∈ N, ¬ ∀ x ∈ commOn ρ N ⊤, ρ a x = ρ n x)
    (hNE : ∀ X : Subgroup G, IsElemAbelian 2 X → NoExcess ρ X (commOn ρ N ⊤))
    (hEE : ∀ X : Subgroup ↥(cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a), IsElemAbelian 2 X →
      Nat.card X * Nat.card (fixSub (subRep (ρ.comp (cenOn ρ ⊤ (commOn ρ N ⊤) ⊔
        Subgroup.zpowers a).subtype) (fixSub ρ N) fun g w hw => hW g w hw) X) ≤
          Nat.card (fixSub ρ N)) :
    False := by
  set K := cenOn ρ ⊤ (commOn ρ N ⊤)
  set K₀ := K ⊔ Subgroup.zpowers a
  have hK : K.Normal := cenOn_commOn_normal hN
  have hNK : N ⊓ K = ⊥ := inf_cenOn_commOn_eq_bot hfa
  have hNK₀ : N ⊓ K₀ = ⊥ := inf_sup_zpowers_eq_bot hN ha2 hfa hout
  obtain ⟨π, -, hπN⟩ := exists_retraction hN hNK₀ (sup_sup_zpowers_eq_top hact)
  obtain ⟨A, ⟨-, hAel, hAb⟩, hAK⟩ : ∃ A ∈ calP ρ, ¬ A ≤ N ⊔ K := by
    by_contra h
    refine notMem_sup_cenOn_commOn hN hout ?_
    have hle : hP ρ ≤ N ⊔ K := iSup₂_le fun A hA => by_contra fun hAK => h ⟨A, hA, hAK⟩
    rw [hH] at hle
    exact hle (Subgroup.mem_top a)
  have hNN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hN]
  have hXA : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ A (commOn ρ N ⊤) := fun g _ u hu =>
    (invariant_commOn_top hNN).2 g (Subgroup.mem_top g) u hu
  have hV : Nat.card V = Nat.card (commOn ρ N ⊤) * Nat.card (fixSub ρ N) := by
    have h := card_inf_mul_card_sup (commOn ρ N ⊤) (fixSub ρ N)
    rw [hcompl.inf_eq_bot, hcompl.sup_eq_top, card_eq_two_pow_finrank ⊥, finrank_bot, pow_zero,
      one_mul, card_top_submodule] at h
    exact h
  have hactE : ∀ g : G, ∀ w ∈ fixSub ρ N, ρ g w = ρ (π g : G) w := fun g w hw => by
    calc ρ g w = ρ (π g : G) (ρ ((π g : G)⁻¹ * g) w) := by rw [glRep_mul_apply, glRep_apply_inv]
      _ = ρ (π g : G) w := by rw [mem_fixSub.1 hw _ (hπN g)]
  have hfixE : fixOn ρ ((A.map π).map K₀.subtype) (fixSub ρ N) = fixOn ρ A (fixSub ρ N) := by
    ext w
    simp only [fixOn, Submodule.mem_inf]
    refine and_congr_right fun hw => ⟨fun h => mem_fixSub.2 fun s hs => (hactE s w hw).trans
      (mem_fixSub.1 h (π s : G) ⟨π s, ⟨s, hs, rfl⟩, rfl⟩), fun h => mem_fixSub.2 ?_⟩
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact (hactE s w hw).symm.trans (mem_fixSub.1 h s hs)
  have hEB := hEE (A.map π) (hAel.map π)
  rw [card_fixSub_subRep (ρ := ρ.comp K₀.subtype) (W := fixSub ρ N) (fun g w hw => hW g w hw),
    fixOn, fixSub_comp_subtype, ← fixOn, hfixE] at hEB
  have hker : π.ker = N := by
    ext g
    rw [MonoidHom.mem_ker]
    refine ⟨fun h => ?_, fun hg => Subtype.ext ?_⟩
    · have h1 := hπN g
      rwa [h, Subgroup.coe_one, inv_one, one_mul] at h1
    · have h1 : ((π g : ↥K₀) : G) ∈ N ⊓ K₀ := ⟨by
        have h2 := N.mul_mem (hπN g) (N.inv_mem hg)
        rwa [mul_inv_cancel_right, inv_mem_iff] at h2, (π g).2⟩
      rw [hNK₀, Subgroup.mem_bot] at h1
      exact h1
  have hcardA : Nat.card A = Nat.card (A.map π) * Nat.card ↥(A ⊓ N) := by
    have h := Subgroup.card_ker_mul_card_of_surjective (π.subgroupMap_surjective A)
    rw [Subgroup.ker_subgroupMap, hker] at h
    have h2 : Nat.card ↥(N.subgroupOf A) = Nat.card ↥(A ⊓ N) := by
      rw [inf_comm, ← Subgroup.subgroupOf_map_subtype]
      exact Nat.card_congr ((N.subgroupOf A).equivMapOfInjective _ A.subtype_injective).toEquiv
    rw [← h, h2, mul_comm]
  have hcen : cenOn ρ A (commOn ρ N ⊤) = A ⊓ K := by
    ext g
    exact ⟨fun h => ⟨h.1, Subgroup.mem_top _, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have hX : Nat.card A * Nat.card (fixOn ρ A (commOn ρ N ⊤)) ≤
      Nat.card (commOn ρ N ⊤) * Nat.card (cenOn ρ A (commOn ρ N ⊤)) := hNE A hAel
  rw [hcen] at hX
  have hoff : Nat.card V ≤ Nat.card A * Nat.card (fixSub ρ A) := hAb.isOffender
  rw [card_fixSub_eq_mul_of_isCompl hcompl hXA (fun g _ w hw => hW g w hw), hV] at hoff
  have key : ∀ a cX cE b k x e : ℕ, 0 < a * cX * cE → a * cX ≤ x * k → b * cE ≤ e →
      x * e ≤ a * (cX * cE) → b ≤ k := fun a cX cE b k x e hpos h1 h2 h3 => by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc a * cX * cE * b = a * cX * (b * cE) := by ring
      _ ≤ x * k * e := Nat.mul_le_mul h1 h2
      _ = k * (x * e) := by ring
      _ ≤ k * (a * (cX * cE)) := Nat.mul_le_mul_left _ h3
      _ = a * cX * cE * k := by ring
  have hBK := key _ _ _ _ _ _ _ (Nat.mul_pos (Nat.mul_pos Nat.card_pos Nat.card_pos)
    Nat.card_pos) hX hEB hoff
  have hAkn : Nat.card A ≤ Nat.card ↥(A ⊓ K) * Nat.card ↥(A ⊓ N) := by
    rw [hcardA]
    exact Nat.mul_le_mul hBK le_rfl
  have hnorm : A ⊓ N ≤ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh =>
      ⟨A.mul_mem (A.mul_mem hg.1 hh.1) (A.inv_mem hg.1), hK.conj_mem h hh.2 g⟩, fun hh => by
        have e : h = g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ := by group
        rw [e]
        exact ⟨A.mul_mem (A.mul_mem (A.inv_mem hg.1) hh.1) (A.inv_mem (A.inv_mem hg.1)),
          hK.conj_mem _ hh.2 g⁻¹⟩⟩
  have hinf : A ⊓ K ⊓ (A ⊓ N) = ⊥ := eq_bot_iff.2 fun g hg => by
    have h : g ∈ N ⊓ K := ⟨hg.2.2, hg.1.2⟩
    rwa [hNK] at h
  have hc := CFSG.ComponentClassification.UnbalancedGS.AHelpers.card_sup_mul_card_inf
    (A ⊓ K) (A ⊓ N) hnorm
  rw [hinf, Subgroup.card_bot, mul_one] at hc
  have heq : A ⊓ K ⊔ A ⊓ N = A :=
    Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) (by rw [hc]; exact hAkn)
  exact hAK (heq.ge.trans (sup_le (inf_le_right.trans le_sup_right)
    (inf_le_right.trans le_sup_left)))

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
