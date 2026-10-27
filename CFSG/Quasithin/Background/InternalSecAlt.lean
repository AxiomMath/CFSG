module

public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.InternalSecIrr

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open

theorem symDn_faithful {n : ℕ} (hn : 5 ≤ n) : (FFModel.symDn n).Faithful := by
  intro (σ : Equiv.Perm (Fin n)) hσ
  by_contra hne
  have hex : ∀ l : List (Fin n), l.length < n → ∃ x, x ∉ l := by
    intro l hl
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ l.toFinset := fun x _ => List.mem_toFinset.2 (h x)
    have h2 := (Finset.card_le_card hsub).trans (List.toFinset_card_le l)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    omega
  obtain ⟨a, ha⟩ : ∃ a, σ⁻¹ a ≠ a := by
    by_contra h
    push Not at h
    exact hne (inv_eq_one.1 (Equiv.ext h))
  set b := σ⁻¹ a with hb
  have hσb : σ b = a := by
    rw [hb, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  obtain ⟨k, hk⟩ := hex [a, b] (by simp; omega)
  obtain ⟨c, hc⟩ := hex [a, b, k, σ k] (by simp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk hc
  set m : G6.PermMod n := Multiplicative.ofAdd (Pi.single b (1 : ZMod 2) + Pi.single k 1) with hm
  have hmval : ∀ x, Multiplicative.toAdd m x =
      (if x = b then (1 : ZMod 2) else 0) + (if x = k then 1 else 0) := fun x => by
    simp [hm, Pi.single_apply]
  have hmc : m ∈ G6.coreMod n := by
    rw [G6.mem_coreMod, hm, toAdd_ofAdd]
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true]
    decide
  obtain ⟨⟨z, hz⟩, -⟩ := hσ m hmc
  have hz' : G6.allOnes n ^ z = G6.permAct n σ m * m⁻¹ := hz
  have hcoord : ∀ i, Multiplicative.toAdd (G6.permAct n σ m * m⁻¹) i =
      Multiplicative.toAdd m (σ⁻¹ i) - Multiplicative.toAdd m i := fun i => by
    rw [sub_eq_add_neg]
    rfl
  have hconst : ∀ i j : Fin n, Multiplicative.toAdd (G6.permAct n σ m * m⁻¹) i =
      Multiplicative.toAdd (G6.permAct n σ m * m⁻¹) j := by
    intro i j
    rw [← hz', toAdd_zpow, Pi.smul_apply, Pi.smul_apply]
    rfl
  have hσc1 : σ⁻¹ c ≠ b := fun h => hc.1 (by rw [← hσb, ← h, ← Equiv.Perm.mul_apply,
    mul_inv_cancel, Equiv.Perm.one_apply])
  have hσc2 : σ⁻¹ c ≠ k := fun h => hc.2.2.2 (by rw [← h, ← Equiv.Perm.mul_apply,
    mul_inv_cancel, Equiv.Perm.one_apply])
  have hab : a ≠ b := ha.symm
  have hak : a ≠ k := fun h => hk.1 h.symm
  have hbk : b ≠ k := fun h => hk.2 h.symm
  have hcb : c ≠ b := hc.2.1
  have hck : c ≠ k := hc.2.2.1
  have hva : Multiplicative.toAdd m a = 0 := by simp [hmval, hab, hak]
  have hvb : Multiplicative.toAdd m b = 1 := by simp [hmval, hbk]
  have hvc : Multiplicative.toAdd m c = 0 := by simp [hmval, hcb, hck]
  have hvσc : Multiplicative.toAdd m (σ⁻¹ c) = 0 := by
    simp only [hmval, hσc1, hσc2, ↓reduceIte, add_zero]
  have h1 := hconst a c
  rw [hcoord, hcoord, ← hb, hva, hvb, hvc, hvσc] at h1
  revert h1
  decide

section Case5

variable {V : Type} [CommGroup V] [Finite V]

theorem alternatingNatural_of_b42Case5 (hV : ∀ v : V, v ^ 2 = 1) {G L A : Subgroup (MulAut V)}
    (hB : B4Hyp G L) (h5 : B42Case5 G A) :
    ∃ n, (n = 5 ∨ n = 7) ∧ AlternatingNatural L ⊤ ⊥ n ∧
      Nonempty (↥L ≃* ↥(alternatingGroup (Fin n))) := by
  obtain ⟨-, hLF, hq, hirr⟩ := hB
  obtain ⟨⟨n, hn, π, hR, -⟩, -⟩ := h5
  have hn5 : 5 ≤ n := by omega
  have hπinj : Function.Injective π := hR.injective_of_faithful (symDn_faithful hn5)
  set e : Equiv.Perm (Fin n) ≃* ↥(ffJ G) := MulEquiv.ofBijective π ⟨hπinj, hR.1⟩ with he
  have hLG : L ≤ G := hLF ▸ quasithinGenFitting_le G
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting G
  have hHG : (ffJ G) ≤ G := B6.ffJ_le G
  have hGH : G ≤ Subgroup.normalizer ((ffJ G) : Set (MulAut V)) := B6.le_normalizer_ffJ G
  have hqo := B1Red.isQuasisimple_to_open hq
  have hLH : L ≤ (ffJ G) := by
    by_contra hLH
    have hcomm := B1Red.commute_of_normal_not_le hqo
      (fun x hx l hl => (Subgroup.mem_normalizer_iff.mp (hGL (hHG hx)) l).mp hl)
      (fun l hl x hx => (Subgroup.mem_normalizer_iff.mp (hGH (hLG hl)) x).mp hx) hLH
    have hHe : (ffJ G) ≤ XMod.eqvAut ↥L V := by
      intro x hx a p
      exact congrArg (fun f : MulAut V => f p) (hcomm x hx a a.2)
    have hodd := odd_card_eqvAut_of_irr hV hirr (exists_noncomm_of_isQuasisimple hq)
    have hdvd := Subgroup.card_dvd_of_le hHe
    have hcardH : Nat.card ↥(ffJ G) = n.factorial := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    have heven : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    rw [hcardH] at hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (heven.trans hdvd))
  have hLHn : (L.subgroupOf (ffJ G)).Normal := by
    refine ⟨fun l hl h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hGL (hHG h.2)) l).mp hl
  set P : Subgroup (Equiv.Perm (Fin n)) := (L.subgroupOf (ffJ G)).comap e.toMonoidHom with hP
  have hPn : P.Normal := Subgroup.Normal.comap hLHn _
  have hPmap : P.map e.toMonoidHom = L.subgroupOf (ffJ G) :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective _
  set ePL : ↥P ≃* ↥L := (e.subgroupMap P).trans
    ((MulEquiv.subgroupCongr hPmap).trans (Subgroup.subgroupOfEquivOfLe hLH)) with hePL
  have : Group.IsPerfect ↥L := ⟨hqo.1⟩
  have hPperf : Group.IsPerfect ↥P :=
    Group.IsPerfect.ofSurjective (f := ePL.symm.toMonoidHom) ePL.symm.surjective
  have hPA : P ≤ alternatingGroup (Fin n) := by
    intro σ hσ
    rw [Equiv.Perm.mem_alternatingGroup]
    have h1 := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp P.subtype)
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact MonoidHom.mem_ker.1 (h1 (Subgroup.mem_top ⟨σ, hσ⟩))
  have : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn5)
  have hAP : alternatingGroup (Fin n) ≤ P := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (P.subgroupOf (alternatingGroup (Fin n))) with h | h
    · exfalso
      have hPb : P = ⊥ := by
        rw [eq_bot_iff]
        intro σ hσ
        have h2 : (⟨σ, hPA hσ⟩ : ↥(alternatingGroup (Fin n))) ∈
            P.subgroupOf (alternatingGroup (Fin n)) := hσ
        rw [h, Subgroup.mem_bot] at h2
        exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
      have : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hqo
      obtain ⟨l, hl1⟩ := exists_ne (1 : ↥L)
      apply hl1
      have h2 : ePL.symm l = 1 := by
        apply Subtype.ext
        have h3 : ((ePL.symm l : ↥P) : Equiv.Perm (Fin n)) ∈
            (⊥ : Subgroup (Equiv.Perm (Fin n))) := by
          rw [← hPb]
          exact (ePL.symm l).2
        exact Subgroup.mem_bot.1 h3
      rw [← ePL.apply_symm_apply l, h2, map_one]
    · intro σ hσ
      have h2 : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin n))) ∈
          P.subgroupOf (alternatingGroup (Fin n)) := by
        rw [h]
        trivial
      exact h2
  set π' : ↥(alternatingGroup (Fin n)) →* ↥L :=
    ePL.toMonoidHom.comp (Subgroup.inclusion hAP) with hπ'
  have hπ'bij : Function.Bijective π' := by
    refine ⟨ePL.injective.comp (Subgroup.inclusion_injective hAP), fun l => ?_⟩
    obtain ⟨x, rfl⟩ := ePL.surjective l
    exact ⟨⟨x, hPA x.2⟩, congrArg ePL (Subtype.ext rfl)⟩
  obtain ⟨-, h1, h2, -, h4, h5', h6, β, hβs, hβk, hβe⟩ := id hR
  refine ⟨n, hn, ⟨π', hπ'bij.2, h1, h2, fun _ _ _ => trivial,
    fun l z hz => h4 ⟨l, hLH l.2⟩ z hz,
    fun (γ : ↥(alternatingGroup (Fin n))) m hm => h5' (γ : Equiv.Perm (Fin n)) m hm,
    fun (γ : ↥(alternatingGroup (Fin n))) m hm => h6 (γ : Equiv.Perm (Fin n)) m hm,
    β, hβs, hβk, fun (γ : ↥(alternatingGroup (Fin n))) u m hu hm hum =>
      hβe (γ : Equiv.Perm (Fin n)) u m hu hm hum⟩,
    ⟨(MulEquiv.ofBijective π' hπ'bij).symm⟩⟩

end Case5

end CFSG.Quasithin.InternalSec
