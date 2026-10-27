module

public import CFSG.Quasithin.Background.FFC11D

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

theorem commutator_mem_of_sq_mem {Ω : Type*} [Group Ω] {G N : Subgroup Ω}
    (hn : ∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) (h2 : ∀ y ∈ G, y ^ 2 ∈ N) :
    ∀ a ∈ G, ∀ b ∈ G, a * b * a⁻¹ * b⁻¹ ∈ N := by
  intro a ha b hb
  have hnorm : (N.subgroupOf G).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hn g g.2 x hx⟩
  have hsq : ∀ q : ↥G ⧸ N.subgroupOf G, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa [pow_two] using h2 y y.2
  have hcomm : ∀ q r : ↥G ⧸ N.subgroupOf G, q * r = r * q := by
    intro q r
    have hq : q⁻¹ = q := inv_eq_of_mul_eq_one_right (hsq q)
    have hr : r⁻¹ = r := inv_eq_of_mul_eq_one_right (hsq r)
    have h1 : q * r = (q * r)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq (q * r))).symm
    rw [mul_inv_rev, hq, hr] at h1
    exact h1
  have h3 := hcomm (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨b, hb⟩)
  have h4 : (QuotientGroup.mk (⟨a * b * a⁻¹ * b⁻¹, G.mul_mem (G.mul_mem (G.mul_mem ha hb)
      (G.inv_mem ha)) (G.inv_mem hb)⟩ : ↥G) : ↥G ⧸ N.subgroupOf G) = 1 := by
    have e : (⟨a * b * a⁻¹ * b⁻¹, G.mul_mem (G.mul_mem (G.mul_mem ha hb) (G.inv_mem ha))
        (G.inv_mem hb)⟩ : ↥G) = ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, h3]
    group
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h4
  exact h4

section Section

variable {V : Type} [CommGroup V] [Finite V]

theorem sectionData (hA21 : AsA21SQTKSection) (hV : ∀ v : V, v ^ 2 = 1)
    {X T M A L : Subgroup (MulAut V)} (hH : CompHyp X T M A L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) :
    B4Hyp (wtLA A L W) (wtL L W) ∧
      (∀ g ∈ wtLA A L W, ∀ l ∈ wtL L W, g * l * g⁻¹ ∈ wtL L W) ∧
      (∀ y ∈ wtLA A L W, y ^ 2 ∈ wtL L W) := by
  obtain ⟨⟨H₀, _, _, hsq, hkg, φ, hφ⟩, hmp, hO2, hFF, hns, hA, hL, hLA⟩ := hH
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLX : L ≤ X := hL.1
  have hAoff : IsFFStarOffender X A := hA.1
  have hAel : IsElemAbelian2 A := hAoff.2.2.1
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  have hAW := a_stab_irr hV hA hLq hLA hW
  have hAZ : ∀ b ∈ A, ∀ w ∈ W ⊓ fixV L, b w ∈ W ⊓ fixV L :=
    isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn)
  have hAWs : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hAZs : A ≤ stabSub (W ⊓ fixV L) := B1.le_stabSub_of_invariant hAZ
  have hMW : L ⊔ A ≤ stabSub W := sup_le hLW hAWs
  have hMZ : L ⊔ A ≤ stabSub (W ⊓ fixV L) := sup_le hLZ hAZs
  have hsupn : ∀ y ∈ L ⊔ A, ∀ l ∈ L, y * l * y⁻¹ ∈ L := by
    intro y hy l hl
    obtain ⟨l', hl', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnL).1 hy
    have e : l' * a * l * (l' * a)⁻¹ = l' * (a * l * a⁻¹) * l'⁻¹ := by group
    rw [e]
    exact L.mul_mem (L.mul_mem hl' (hAn a ha l hl)) (L.inv_mem hl')
  have hsq2 : ∀ y ∈ L ⊔ A, y ^ 2 ∈ L := B1Red.sq_mem_of_mem_sup hAnL hAel.2
  have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
  obtain ⟨ℓ, hℓs, hℓk⟩ := exists_surj_autSec hLW hLZ
  have hmapL := B5.map_secHom_eq_autSec (L ⊔ A) hMW hMZ (le_sup_left : L ≤ L ⊔ A)
  have hrange := B5.range_secHom (L ⊔ A) hMW hMZ
  have hLG : autSec L W (W ⊓ fixV L) ≤ autSec (L ⊔ A) W (W ⊓ fixV L) :=
    autSec_mono le_sup_left W _
  have hLbn : ∀ g ∈ autSec (L ⊔ A) W (W ⊓ fixV L), ∀ l ∈ autSec L W (W ⊓ fixV L),
      g * l * g⁻¹ ∈ autSec L W (W ⊓ fixV L) := by
    intro g hg l hl
    rw [← hrange] at hg
    obtain ⟨m, rfl⟩ := hg
    rw [← hmapL] at hl ⊢
    obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.1 hl
    refine Subgroup.mem_map.2 ⟨m * l' * m⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf] at hl' ⊢
    exact hsupn m m.2 l' hl'
  have hHb2 : ∀ y ∈ autSec (L ⊔ A) W (W ⊓ fixV L), y ^ 2 ∈ autSec L W (W ⊓ fixV L) := by
    intro y hy
    rw [← hrange] at hy
    obtain ⟨m, rfl⟩ := hy
    rw [← hmapL]
    refine Subgroup.mem_map.2 ⟨m ^ 2, ?_, by simp [map_pow]⟩
    rw [Subgroup.mem_subgroupOf]
    exact hsq2 m m.2
  have hnt : Nontrivial ↥(autSec L W (W ⊓ fixV L)) := nontrivial_autSec hW
  have hne : ℓ.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    obtain ⟨x, rfl⟩ := hℓs a
    obtain ⟨y, rfl⟩ := hℓs b
    apply hab
    have hx : x ∈ ℓ.ker := by rw [htop]; trivial
    have hy : y ∈ ℓ.ker := by rw [htop]; trivial
    rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
  have hcent : ℓ.ker ≤ Subgroup.center ↥L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hLq ℓ.ker hne
  have hLbq : CFSG.IsQuasisimple ↥(autSec L W (W ⊓ fixV L)) :=
    CFSG.LocalCores.isQuasisimple_of_surjective (B1Red.isQuasisimple_of_open hLq) ℓ hℓs hcent
  obtain ⟨hinv, -, hlt, hirr⟩ := mem_irrPlus_top_iff.1 hW
  have hIrr : XMod.IsIrrSec ↥(autSec L W (W ⊓ fixV L)) (⊥ : Subgroup (Sec W (W ⊓ fixV L))) ⊤ :=
    B5.isIrrSec_autSec hlt hirr hLW hLZ
  have hO2G : pCoreOf 2 (autSec (L ⊔ A) W (W ⊓ fixV L)) = ⊥ := n1_pCoreOf_eq_bot hS2 hLG hIrr
  have hFstar : quasithinGenFitting (autSec (L ⊔ A) W (W ⊓ fixV L)) =
      autSec L W (W ⊓ fixV L) :=
    B1Red.quasithinGenFitting_eq_of_two_quot hLG hLbn (B1Red.isQuasisimple_to_open hLbq) hHb2 hO2G
  have hSQL : SQTKGroup ↥L := sqtk_subgroup hA21 ⟨hsq, hkg⟩ φ hφ hLX (B1Red.isQuasisimple_of_open hLq)
  have hSQLt : SQTKGroup ↥(autSec L W (W ⊓ fixV L)) := by
    let π : ↥(⊤ : Subgroup ↥L) →* ↥(autSec L W (W ⊓ fixV L)) := ℓ.comp (⊤ : Subgroup ↥L).subtype
    refine sqtk_of_surj hA21 hSQL π (fun y => ?_) hLbq
    obtain ⟨x, hx⟩ := hℓs y
    exact ⟨⟨x, trivial⟩, hx⟩
  have hSQG : SQTKGroup ↥(autSec (L ⊔ A) W (W ⊓ fixV L)) := by
    set G := autSec (L ⊔ A) W (W ⊓ fixV L) with hGdef
    set Lt := autSec L W (W ⊓ fixV L) with hLtdef
    have hnorm : (Lt.subgroupOf G).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have := hLbn (g : MulAut (Sec W (W ⊓ fixV L))) g.2 x hx
      simpa using this
    have hq2 : IsPGroup 2 (↥G ⧸ Lt.subgroupOf G) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H y =>
        refine ⟨1, ?_⟩
        rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using hHb2 y y.2
    let e : ↥(Lt.subgroupOf G) ≃* ↥Lt := Subgroup.subgroupOfEquivOfLe hLG
    have hLm : SQTKGroup ↥(Lt.subgroupOf G) := by
      refine ⟨fun p hp hp2 => ?_, hSQLt.2.of_mulEquiv e⟩
      show CFSG.Open.pRank p (⊤ : Subgroup ↥(Lt.subgroupOf G)) ≤ 2
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
      exact hSQLt.1 p hp hp2
    exact ⟨B5.sqt_of_two_quotient _ hq2 hLm.1, B5.kGroup_of_two_quotient _ hq2 hLm.2⟩
  exact ⟨⟨hSQG, hFstar.symm, hLbq, hIrr⟩, hLbn, hHb2⟩

omit [Finite V] in
theorem alt_not_comm {n : ℕ} (hn : 5 ≤ n) :
    ¬ ∀ a ∈ alternatingGroup (Fin n), ∀ b ∈ alternatingGroup (Fin n), a * b = b * a := by
  intro h
  have h5 : 5 ≤ Nat.card (Fin n) := by simpa using hn
  have hperf : Group.IsPerfect ↥(alternatingGroup (Fin n)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top h5)
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup h5
  have hnt : Nontrivial ↥(alternatingGroup (Fin n)) := hs.toNontrivial
  refine Group.IsPerfect.not_isMulCommutative ↥(alternatingGroup (Fin n))
    (IsMulCommutative.of_comm fun a b => ?_)
  exact Subtype.ext (h a a.2 b b.2)

omit [Finite V] in
theorem wtL_eq_alt {S : Type} [CommGroup S] {G Lt J : Subgroup (MulAut S)} {n : ℕ} (hn : 5 ≤ n)
    {π : Equiv.Perm (Fin n) →* ↥J} (hπi : Function.Injective π) (hπs : Function.Surjective π)
    (hJG : J ≤ G) (hJn : ∀ g ∈ G, ∀ j ∈ J, g * j * g⁻¹ ∈ J)
    (hLn : ∀ g ∈ G, ∀ l ∈ Lt, g * l * g⁻¹ ∈ Lt) (hG2 : ∀ y ∈ G, y ^ 2 ∈ Lt)
    (hLG : Lt ≤ G) (hLq : CFSG.Open.IsQuasisimple ↥Lt) :
    Lt = (alternatingGroup (Fin n)).map (J.subtype.comp π) := by
  have h5 : 5 ≤ Nat.card (Fin n) := by simpa using hn
  set ψ : Equiv.Perm (Fin n) →* MulAut S := J.subtype.comp π with hψ
  have hψi : Function.Injective ψ := J.subtype_injective.comp hπi
  have hψG : ∀ σ, ψ σ ∈ G := fun σ => hJG (π σ).2
  have hψrange : ∀ x ∈ J, ∃ σ, ψ σ = x := by
    intro x hx
    obtain ⟨σ, hσ⟩ := hπs ⟨x, hx⟩
    exact ⟨σ, congrArg Subtype.val hσ⟩
  have hψJ : ∀ σ, ψ σ ∈ J := fun σ => (π σ).2
  have hcomm : commutator (Equiv.Perm (Fin n)) ≤ Lt.comap ψ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    show ψ ⁅g, h⁆ ∈ Lt
    rw [map_commutatorElement, commutatorElement_def]
    exact commutator_mem_of_sq_mem hLn hG2 (ψ g) (hψG g) (ψ h) (hψG h)
  have hAalt : alternatingGroup (Fin n) ≤ Lt.comap ψ := by
    rw [← alternatingGroup.commutator_perm_eq h5]
    exact hcomm
  have hAL : (alternatingGroup (Fin n)).map ψ ≤ Lt := by
    rw [Subgroup.map_le_iff_le_comap]
    exact hAalt
  have hK : ((J ⊓ Lt).subgroupOf Lt).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hJn g (hLG g.2) x hx.1, hLn g (hLG g.2) x hx.2⟩⟩
  have hLJ : Lt ≤ J := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hLq
      ((J ⊓ Lt).subgroupOf Lt) with hc | htop
    · exfalso
      apply alt_not_comm hn
      intro a ha b hb
      have haJ : ψ a ∈ J ⊓ Lt := ⟨hψJ a, hAL (Subgroup.mem_map_of_mem _ ha)⟩
      have hbJ : ψ b ∈ J ⊓ Lt := ⟨hψJ b, hAL (Subgroup.mem_map_of_mem _ hb)⟩
      have hmem : (⟨ψ a, haJ.2⟩ : ↥Lt) ∈ (J ⊓ Lt).subgroupOf Lt := haJ
      have hcen := Subgroup.mem_center_iff.1 (hc hmem) ⟨ψ b, hbJ.2⟩
      apply hψi
      rw [map_mul, map_mul]
      exact (congrArg Subtype.val hcen).symm
    · intro x hx
      have : (⟨x, hx⟩ : ↥Lt) ∈ (J ⊓ Lt).subgroupOf Lt := by rw [htop]; trivial
      exact this.1
  have hLA : Lt ≤ (alternatingGroup (Fin n)).map ψ := by
    have hsub : (⊤ : Subgroup ↥Lt) ≤ ((alternatingGroup (Fin n)).map ψ).subgroupOf Lt := by
      rw [← hLq.1, commutator_def, Subgroup.commutator_le]
      intro g _ h _
      obtain ⟨σ, hσ⟩ := hψrange g (hLJ g.2)
      obtain ⟨τ, hτ⟩ := hψrange h (hLJ h.2)
      rw [Subgroup.mem_subgroupOf]
      have e1 : ((⁅g, h⁆ : ↥Lt) : MulAut S) = ψ ⁅σ, τ⁆ := by
        rw [map_commutatorElement, hσ, hτ]
        rfl
      rw [e1]
      refine Subgroup.mem_map_of_mem _ ?_
      rw [← alternatingGroup.commutator_perm_eq h5, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top σ) (Subgroup.mem_top τ)
    intro x hx
    have := hsub (Subgroup.mem_top (⟨x, hx⟩ : ↥Lt))
    exact this
  exact le_antisymm hLA hAL

end Section

end B69

end CFSG.Quasithin
