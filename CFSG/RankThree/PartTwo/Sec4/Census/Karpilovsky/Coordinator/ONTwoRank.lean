module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.ONSylowCenter
public import Certificates.Certificate291400

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank

open CFSG.ONSchreier CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four (TabRep exists_getElem!_of_mem allBelow_eq_true)

theorem commMat_getElem! {I : Array Tab} {i j : ℕ} (hi : i < I.size) (hj : j < I.size) :
    ((commMat I)[i]!)[j]! = (comp 32 I[i]! I[j]! == comp 32 I[j]! I[i]!) := by
  simp [commMat, getElem!_pos, hi, hj]

theorem thirdOK_of_check (h : noE16Check () = true) {i j : ℕ} (hi : i < (invTabs ()).size)
    (hj : j < (invTabs ()).size) (hij : ((commMat (invTabs ()))[i]!)[j]! = true) (hne : i ≠ j) :
    thirdOK (invTabs ()) (commMat (invTabs ())) i j = true := by
  unfold noE16Check at h
  dsimp only at h
  rw [allBelow_eq_true] at h
  have h1 := h i hi
  rw [allBelow_eq_true] at h1
  have h2 := h1 j hj
  rw [hij] at h2
  simpa [hne] using h2

theorem fourthOK_of_thirdOK {I : Array Tab} {C : Array (Array Bool)} {i j k : ℕ}
    (h : thirdOK I C i j = true) (hk : k < I.size) (hik : (C[i]!)[k]! = true)
    (hjk : (C[j]!)[k]! = true) (hki : k ≠ i) (hkj : k ≠ j) (hab : I[k]! ≠ comp 32 I[i]! I[j]!) :
    fourthOK I C i j k = true := by
  unfold thirdOK at h
  dsimp only at h
  rw [allBelow_eq_true] at h
  have h1 := h k hk
  rw [hik, hjk] at h1
  simpa [hki, hkj, hab] using h1

theorem mem_of_fourthOK {I : Array Tab} {C : Array (Array Bool)} {i j k l : ℕ}
    (h : fourthOK I C i j k = true) (hl : l < I.size) (hil : (C[i]!)[l]! = true)
    (hjl : (C[j]!)[l]! = true) (hkl : (C[k]!)[l]! = true) :
    I[l]! = I[i]! ∨ I[l]! = I[j]! ∨ I[l]! = I[k]! ∨ I[l]! = comp 32 I[i]! I[j]! ∨
      I[l]! = comp 32 I[i]! I[k]! ∨ I[l]! = comp 32 I[j]! I[k]! ∨
      I[l]! = comp 32 (comp 32 I[i]! I[j]!) I[k]! := by
  unfold fourthOK at h
  dsimp only at h
  rw [allBelow_eq_true] at h
  have h1 := h l hl
  rw [hil, hjl, hkl] at h1
  simpa [or_assoc] using h1

section T32


theorem exists_invTabs {x : Equiv.Perm (Fin 32)} (hx : x ∈ onT32Chain.originalSubgroup)
    (h2 : x * x = 1) (h1 : x ≠ 1) : ∃ i < (invTabs ()).size, TabRep (invTabs ())[i]! x := by
  obtain ⟨t, ht, hr⟩ := t32_enumerates.complete x hx
  have e1 : (comp 32 t t == idTab 32) = true :=
    ((hr.comp hr).beq_iff CFSG.ComponentClassification.PSL3Four.TabRep.idTab).2 h2
  have e2 : (t == idTab 32) = false := by
    cases hb : (t == idTab 32)
    · rfl
    · exact absurd ((hr.beq_iff CFSG.ComponentClassification.PSL3Four.TabRep.idTab).1 hb) h1
  have hmem : t ∈ (invTabs ()).toList := by
    rw [Array.mem_toList_iff, invTabs, Array.mem_filter]
    exact ⟨Array.mem_toList_iff.1 ht, by simp [e1, e2]⟩
  obtain ⟨i, hi, hti⟩ := exists_getElem!_of_mem hmem
  exact ⟨i, hi, hti ▸ hr⟩


theorem card_le_eight_of_hom {A : Type*} [Group A] (hcomm : ∀ a b : A, a * b = b * a)
    (hsq : ∀ a : A, a * a = 1) (φ : A →* Equiv.Perm (Fin 32)) (hφ : Function.Injective φ)
    (hmem : ∀ a, φ a ∈ onT32Chain.originalSubgroup) : Nat.card A ≤ 8 := by
  classical
  have : Finite A := Finite.of_injective φ hφ
  have := Fintype.ofFinite A
  refine Nat.le_of_not_lt fun hlt => ?_
  have hex : ∀ S : List A, S.length ≤ 8 → ∃ x : A, x ∉ S := by
    intro S hS
    by_contra hall
    have h1 : (Finset.univ : Finset A) ⊆ S.toFinset := fun x _ =>
      List.mem_toFinset.2 (not_not.1 fun hx => hall ⟨x, hx⟩)
    have h2 := (Finset.card_le_card h1).trans (List.toFinset_card_le S)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
    omega
  obtain ⟨a, ha⟩ := hex [1] (by simp)
  obtain ⟨b, hb⟩ := hex [1, a] (by simp)
  obtain ⟨c, hc⟩ := hex [1, a, b, a * b] (by simp)
  obtain ⟨d, hd⟩ := hex [1, a, b, c, a * b, a * c, b * c, a * b * c] (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb hc hd
  have hinv : ∀ x : A, x ≠ 1 → ∃ i < (invTabs ()).size, TabRep (invTabs ())[i]! (φ x) :=
    fun x hx => exists_invTabs (hmem x) (by rw [← map_mul, hsq, map_one])
      (fun h => hx ((map_eq_one_iff φ hφ).1 h))
  obtain ⟨i, hi, hri⟩ := hinv a ha
  obtain ⟨j, hj, hrj⟩ := hinv b hb.1
  obtain ⟨k, hk, hrk⟩ := hinv c hc.1
  obtain ⟨l, hl, hrl⟩ := hinv d hd.1
  have hC : ∀ {x y : A} {p q : ℕ} (hp : p < (invTabs ()).size) (hq : q < (invTabs ()).size),
      TabRep (invTabs ())[p]! (φ x) → TabRep (invTabs ())[q]! (φ y) →
        ((commMat (invTabs ()))[p]!)[q]! = true := by
    intro x y p q hp hq hx hy
    rw [commMat_getElem! hp hq]
    exact ((hx.comp hy).beq_iff (hy.comp hx)).2 (by rw [← map_mul, ← map_mul, hcomm])
  have hE : ∀ {x y : A} {t s : Tab}, TabRep t (φ x) → TabRep s (φ y) → t = s → x = y :=
    fun hx hy h => hφ ((hx.eq_iff hy).1 h)
  have hne : ∀ {x y : A} {p q : ℕ}, TabRep (invTabs ())[p]! (φ x) →
      TabRep (invTabs ())[q]! (φ y) → x ≠ y → p ≠ q := by
    rintro x y p q hx hy hxy rfl
    exact hxy (hE hx hy rfl)
  have hmul : ∀ {x y : A} {t s : Tab}, TabRep t (φ x) → TabRep s (φ y) →
      TabRep (comp 32 t s) (φ (x * y)) := by
    intro x y t s hx hy
    rw [map_mul]
    exact hx.comp hy
  have h3 := thirdOK_of_check Certificates.certificate291400 hi hj (hC hi hj hri hrj)
    (hne hri hrj (Ne.symm hb.2))
  have h4 := fourthOK_of_thirdOK h3 hk (hC hi hk hri hrk) (hC hj hk hrj hrk)
    (hne hrk hri hc.2.1) (hne hrk hrj hc.2.2.1) (fun h => hc.2.2.2 (hE hrk (hmul hri hrj) h))
  rcases mem_of_fourthOK h4 hl (hC hi hl hri hrl) (hC hj hl hrj hrl) (hC hk hl hrk hrl) with
    e | e | e | e | e | e | e
  · exact hd.2.1 (hE hrl hri e)
  · exact hd.2.2.1 (hE hrl hrj e)
  · exact hd.2.2.2.1 (hE hrl hrk e)
  · exact hd.2.2.2.2.1 (hE hrl (hmul hri hrj) e)
  · exact hd.2.2.2.2.2.1 (hE hrl (hmul hri hrk) e)
  · exact hd.2.2.2.2.2.2.1 (hE hrl (hmul hrj hrk) e)
  · exact hd.2.2.2.2.2.2.2 (hE hrl (hmul (hmul hri hrj) hrk) e)

end T32

theorem card_le_eight_of_hom_Pv {A : Type*} [Group A] (hcomm : ∀ a b : A, a * b = b * a)
    (hsq : ∀ a : A, a * a = 1) (ψ₀ : A →* Pv) (hψ₀ : Function.Injective ψ₀) :
    Nat.card A ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ψ₀.range := by
    intro y
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← ha, ← map_pow, sq, hsq, map_one]
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Pv P onTSylow
  let ψ : A →* Pv := (MulAut.conj g).toMonoidHom.comp ψ₀
  have hψ : ∀ a : A, ψ a ∈ onT.subgroupOf Pv := by
    intro a
    rw [← onTSylow_coe, ← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul (ψ₀ a) (MulAut.conj g) (P : Subgroup Pv)
      (hP (MonoidHom.mem_range.2 ⟨a, rfl⟩))
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply hψ₀
    have h : (MulAut.conj g) (ψ₀ a) = (MulAut.conj g) (ψ₀ b) := hab
    exact (MulAut.conj g).injective h
  let χ : A →* onT :=
    (Subgroup.subgroupOfEquivOfLe onT_le).toMonoidHom.comp (ψ.codRestrict _ hψ)
  have hχ : Function.Injective χ := by
    intro a b hab
    apply hψinj
    have h := congrArg Subtype.val hab
    exact Subtype.ext h
  refine card_le_eight_of_hom hcomm hsq (rhoT.comp χ) (fun a b hab => ?_) (fun a => ?_)
  · have h : rhoT (χ a) = rhoT (χ b) := hab
    exact hχ (rhoT_injective h)
  · rw [← rhoT_range]
    exact MonoidHom.mem_range.2 ⟨χ a, rfl⟩

theorem card_le_eight_of_mulEquiv_Pv {G : Type*} [Group G] (e : G ≃* Pv) (E : Subgroup G)
    (hE : CFSG.Assembly.IsElemAbelian 2 E) : Nat.card E ≤ 8 := by
  have hsq : ∀ a : E, a * a = 1 := fun a => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq]
    exact hE.2 a a.2)
  exact card_le_eight_of_hom_Pv (fun a b => hE.1.is_comm.comm a b) hsq
    (e.toMonoidHom.comp E.subtype) (e.injective.comp Subtype.val_injective)

theorem card_le_eight_of_isElemAbelian_ON : ∀ E : Subgroup CFSG.Blueprint.NativeSporadic.ON,
    CFSG.Assembly.IsElemAbelian 2 E → Nat.card E ≤ 8 :=
  fun E hE => card_le_eight_of_mulEquiv_Pv (by exact onEquivPv) E hE

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank
