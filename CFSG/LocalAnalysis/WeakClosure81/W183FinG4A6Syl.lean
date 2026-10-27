module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4A6S6
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54AS
import CFSG.Quasithin.EmptyFaithful.S146xB2Aut
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

theorem w183finG4A6_isSylowIn_map {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {p : ℕ} {P X : Subgroup G} (h : IsSylowIn p P X) :
    IsSylowIn p (P.map f) (X.map f) := by
  refine ⟨Subgroup.map_mono h.le, h.isPGroup.map f, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective P X hf]
  exact h.not_dvd_relIndex

theorem w183finG4A6_exists_inner_conj_le_sylow {G : Type} [Group G] [Finite G]
    {X I P B : Subgroup G} (hIX : I ≤ X) (hIn : (I.subgroupOf X).Normal)
    (hidx : I.relIndex X = 2) (hP : IsSylowIn 2 P X) (hPI : ¬ P ≤ I) (hBX : B ≤ X)
    (hB : IsPGroup 2 ↥B) :
    ∃ g ∈ I, B.map (MulAut.conj g).toMonoidHom ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hBQ⟩ := exists_isSylowIn_ge 2 hBX hB
  obtain ⟨x, hxX, hxQ⟩ := Ch1Sec3.exists_conj_of_isSylowIn hP hQ
  have hIP_le : I ⊔ P ≤ X := sup_le hIX hP.le
  have hmul := Subgroup.relIndex_mul_relIndex (H := I) (K := I ⊔ P) (L := X)
    le_sup_left hIP_le
  have hdvd : I.relIndex (I ⊔ P) ∣ 2 := ⟨(I ⊔ P).relIndex X, by rw [hmul, hidx]⟩
  have hne : I.relIndex (I ⊔ P) ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact hPI (le_trans le_sup_right h1)
  have htwo : I.relIndex (I ⊔ P) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  have hXle : X ≤ I ⊔ P := by
    have h1 : (I ⊔ P).relIndex X = 1 := by
      have h2 := hmul
      rw [htwo, hidx] at h2
      omega
    exact (Subgroup.relIndex_eq_one).1 h1
  have hXIP : I ⊔ P = X := le_antisymm hIP_le hXle
  have hxIP : x ∈ I ⊔ P := by rw [hXIP]; exact hxX
  have hnormI : P ≤ Subgroup.normalizer (I : Set G) :=
    hP.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hIX).1 hIn)
  obtain ⟨i, hiI, p, hpP, hip⟩ :=
    (Ch1Sec3.mem_sup_iff_of_le_normalizer hnormI).1 hxIP
  refine ⟨i⁻¹, I.inv_mem hiI, ?_⟩
  rintro b ⟨c, hc, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hcQ : c ∈ Q := hBQ hc
  have hxc : x⁻¹ * c * x ∈ P := (hxQ c).1 hcQ
  have hxeq : x⁻¹ * c * x = p⁻¹ * (i⁻¹ * c * i) * p := by
    rw [hip]; group
  rw [hxeq] at hxc
  have hthis : i⁻¹ * c * i = p * (p⁻¹ * (i⁻¹ * c * i) * p) * p⁻¹ := by group
  rw [hthis]
  exact P.mul_mem (P.mul_mem hpP hxc) (P.inv_mem hpP)

theorem w183finG4A6_exists_inner_conj_sylow {G : Type} [Group G] [Finite G]
    {X I P Q : Subgroup G} (hIX : I ≤ X) (hIn : (I.subgroupOf X).Normal)
    (hidx : I.relIndex X = 2) (hP : IsSylowIn 2 P X) (hPI : ¬ P ≤ I) (hQ : IsSylowIn 2 Q X) :
    ∃ g ∈ I, Q.map (MulAut.conj g).toMonoidHom = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgI, hgQ⟩ :=
    w183finG4A6_exists_inner_conj_le_sylow hIX hIn hidx hP hPI hQ.le hQ.isPGroup
  refine ⟨g, hgI, Subgroup.eq_of_le_of_card_ge hgQ ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, IsSylowIn.card_eq hQ,
    IsSylowIn.card_eq hP]

theorem w183finG4A6_br2NormalConj_autS6 {M : Type} [Group M]
    (e : M ≃* alternatingGroup (Fin 6)) : Br2NormalConj M (w183finG4A6AutS6 e) := by
  classical
  let X₀ : Subgroup (MulAut M) := w183finG4A6AutS6 e
  let I₀ : Subgroup (MulAut M) := innAutOf M
  change Br2NormalConj M X₀
  intro P₀ hP₀ A hA_le hA_el hA8
  obtain ⟨f, hf_inj, -, hf_surj, hf_inn, hf_s6⟩ := w183finG4A6_exists_model e
  haveI : Finite M := Finite.of_injective e e.injective
  haveI : Finite (MulAut M) :=
    Finite.of_injective (fun α : MulAut M => (α : M → M)) DFunLike.coe_injective
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX₀map : X₀.map f = A6Facts.s6 := by
    ext y
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact (hf_s6 γ).1 hγ
    · intro hy
      obtain ⟨γ, hγ⟩ := hf_surj y (A6Facts.s6_le_autA6 hy)
      exact ⟨γ, (hf_s6 γ).2 (hγ ▸ hy), hγ⟩
  have hI₀map : I₀.map f = A6Models.psl29 := by
    ext y
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact (hf_inn γ).1 hγ
    · intro hy
      obtain ⟨γ, hγ⟩ := hf_surj y (A6Facts.psl29_le_autA6 hy)
      exact ⟨γ, (hf_inn γ).2 (hγ ▸ hy), hγ⟩
  have hI₀X₀ : I₀ ≤ X₀ := by
    intro γ hγ
    rw [show I₀ = innAutOf M from rfl] at hγ
    rw [hf_inn] at hγ
    rw [show X₀ = w183finG4A6AutS6 e from rfl, hf_s6]
    exact A6Facts.psl29_le_s6 hγ
  have hX₀card : Nat.card X₀ = 720 := by
    rw [← Subgroup.card_map_of_injective (K := X₀) (f := f) hf_inj, hX₀map,
      w183finG4A6_model_card_s6]
  have hI₀card : Nat.card I₀ = 360 := by
    rw [← Subgroup.card_map_of_injective (K := I₀) (f := f) hf_inj, hI₀map,
      A6Facts.card_psl29]
  have hIn : (I₀.subgroupOf X₀).Normal := (innAutOf_normal M).subgroupOf X₀
  have hidx : I₀.relIndex X₀ = 2 := by
    have hmap := Subgroup.relIndex_map_map_of_injective (H := I₀) (K := X₀) hf_inj
    rw [hI₀map, hX₀map] at hmap
    rw [← hmap, (w183finG4A6_model_psl_s6).2]
  have hP₀card : Nat.card P₀ = 16 := by
    rw [IsSylowIn.card_eq hP₀, hX₀card, CFSG.QuasithinUnique.Out21.A6.factorization_720]
    norm_num
  have hPI : ¬ P₀ ≤ I₀ := by
    intro hle
    have hdiv : Nat.card P₀ ∣ Nat.card I₀ := Subgroup.card_dvd_of_le hle
    rw [hP₀card, hI₀card] at hdiv
    norm_num at hdiv
  obtain ⟨g, hgI, hgA⟩ :=
    w183finG4A6_exists_inner_conj_le_sylow hI₀X₀ hIn hidx hP₀ hPI hA_le hA_el.isPGroup
  have hAg_le : autConj g A ≤ P₀ := by
    rw [autConj]
    exact hgA
  have hAcard : Nat.card (autConj g A) = 8 := by
    have h1 : Nat.card (autConj g A) = Nat.card A := by
      rw [autConj]
      exact Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [h1]
    have hle := card_le_eight_of_alt_six e hA_el
    omega
  have hrel : (autConj g A).relIndex P₀ = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := autConj g A) (K := P₀)
    rw [inf_eq_left.2 hAg_le, hAcard, hP₀card] at h1
    omega
  have hnorm : ((autConj g A).subgroupOf P₀).Normal :=
    Subgroup.normal_of_index_eq_two (by simpa [Subgroup.relIndex] using hrel)
  refine ⟨g, hgI, hAg_le, ?_⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAg_le).1 hnorm

end CFSG.LocalAnalysis.WeakClosure81

end
