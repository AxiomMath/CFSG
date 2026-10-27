module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin.H13.KGMinPar

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

variable {X : Type} [Group X]

theorem false_of_sup [Finite X] {S P A B : Subgroup X} (hP : P ∈ uFam ⊤ S) (hSA : S ≤ A)
    (hSB : S ≤ B) (hAP : A < P) (hBP : B < P) (hAB : A ⊔ B = P) : False := by
  obtain ⟨-, -, hone⟩ := hP
  obtain ⟨M, hM⟩ := maxOver_ncard_eq_one_iff.mp hone
  obtain ⟨hMmax, -, huniq⟩ := isUniqueMaxOver_iff.mp hM
  obtain ⟨N₁, hN₁, hAN₁⟩ := exists_isMaxSubgroupIn hAP
  obtain ⟨N₂, hN₂, hBN₂⟩ := exists_isMaxSubgroupIn hBP
  have h1 : N₁ = M := huniq N₁ hN₁ (hSA.trans hAN₁)
  have h2 : N₂ = M := huniq N₂ hN₂ (hSB.trans hBN₂)
  have hPM : P ≤ M := hAB ▸ sup_le (h1 ▸ hAN₁) (h2 ▸ hBN₂)
  exact absurd hMmax.1 (not_lt_of_ge hPM)

theorem sup_eq_top [Finite X] {L S : Subgroup X} (hL2 : L.index ∣ 2) (hS : IsSylowTwoOf S ⊤) :
    L ⊔ S = ⊤ := by
  obtain ⟨-, hodd⟩ := K1.isSylowTwoOf_top_iff.mp hS
  have h2 : (L ⊔ S).index ∣ S.index := Subgroup.index_dvd_of_le le_sup_right
  have h3 : (L ⊔ S).index ∣ 2 := (Subgroup.index_dvd_of_le le_sup_left).trans hL2
  rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
  · exact Subgroup.index_eq_one.mp h
  · exact absurd (h ▸ h2) hodd

theorem inf_sup_eq {L S P : Subgroup X} [L.Normal] (hLS : L ⊔ S = ⊤) (hSP : S ≤ P) :
    (P ⊓ L) ⊔ S = P := by
  refine le_antisymm (sup_le inf_le_left hSP) fun p hp => ?_
  have hmem : p ∈ ((L ⊔ S : Subgroup X) : Set X) := by rw [hLS]; trivial
  rw [Subgroup.normal_mul] at hmem
  obtain ⟨l, hl, s, hs, rfl⟩ := hmem
  have hlP : l ∈ P := by simpa using P.mul_mem hp (P.inv_mem (hSP hs))
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlP, hl⟩) (Subgroup.mem_sup_right hs)

theorem sup_inf_le {L S R : Subgroup X} (hRL : R ≤ L) (hSL : S ⊓ L ≤ R)
    (hSN : S ≤ Subgroup.normalizer (R : Set X)) : (R ⊔ S) ⊓ L ≤ R := by
  rintro x ⟨hx, hxL⟩
  have hmem : x ∈ ((R ⊔ S : Subgroup X) : Set X) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R S hSN] at hmem
  obtain ⟨r, hr, s, hs, rfl⟩ := hmem
  have hsL : s ∈ L := by simpa using L.mul_mem (L.inv_mem (hRL hr)) hxL
  exact R.mul_mem hr (hSL ⟨hs, hsL⟩)

theorem false_of_pair [Finite X] {L S P R₁ R₂ : Subgroup X} [L.Normal] (hP : P ∈ uFam ⊤ S)
    (hLS : L ⊔ S = ⊤) (h₁ : R₁ ≤ P ⊓ L) (h₂ : R₂ ≤ P ⊓ L) (hT₁ : S ⊓ L ≤ R₁)
    (hT₂ : S ⊓ L ≤ R₂) (hN₁ : S ≤ Subgroup.normalizer (R₁ : Set X))
    (hN₂ : S ≤ Subgroup.normalizer (R₂ : Set X)) (hne₁ : R₁ ≠ P ⊓ L) (hne₂ : R₂ ≠ P ⊓ L)
    (hsup : R₁ ⊔ R₂ = P ⊓ L) : False := by
  have hSP : S ≤ P := hP.2.1.le
  have hlt : ∀ R : Subgroup X, R ≤ P ⊓ L → S ⊓ L ≤ R →
      S ≤ Subgroup.normalizer (R : Set X) → R ≠ P ⊓ L → R ⊔ S < P := by
    intro R hR hTR hNR hne
    refine lt_of_le_of_ne (sup_le (hR.trans inf_le_left) hSP) fun h => hne ?_
    refine le_antisymm hR ?_
    calc P ⊓ L = (R ⊔ S) ⊓ L := by rw [h]
      _ ≤ R := sup_inf_le (hR.trans inf_le_right) hTR hNR
  have hA := hlt R₁ h₁ hT₁ hN₁ hne₁
  have hB := hlt R₂ h₂ hT₂ hN₂ hne₂
  refine false_of_sup hP le_sup_right le_sup_right hA hB (le_antisymm (sup_le hA.le hB.le) ?_)
  calc P = (P ⊓ L) ⊔ S := (inf_sup_eq hLS hSP).symm
    _ = (R₁ ⊔ R₂) ⊔ S := by rw [hsup]
    _ ≤ (R₁ ⊔ S) ⊔ (R₂ ⊔ S) :=
      sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
        (le_sup_right.trans le_sup_left)

@[expose] def canon (T L : Subgroup X) (o : ℕ) : Subgroup X :=
  ⨅ (W : Subgroup X) (_ : T ≤ W ∧ W ≤ L ∧ Nat.card W = o), W

theorem canon_le {T L W : Subgroup X} {o : ℕ} (hTW : T ≤ W) (hWL : W ≤ L)
    (ho : Nat.card W = o) : canon T L o ≤ W :=
  iInf₂_le W ⟨hTW, hWL, ho⟩

theorem le_canon {T L : Subgroup X} {o : ℕ} : T ≤ canon T L o :=
  le_iInf₂ fun _ h => h.1

theorem le_canon_of {T L R : Subgroup X} {o : ℕ}
    (h : ∀ W : Subgroup X, T ≤ W → W ≤ L → Nat.card W = o → R ≤ W) : R ≤ canon T L o :=
  le_iInf₂ fun W hW => h W hW.1 hW.2.1 hW.2.2

theorem conj_mem_canon {T L : Subgroup X} {o : ℕ} {s : X}
    (hsT : s ∈ Subgroup.normalizer (T : Set X)) (hsL : s ∈ Subgroup.normalizer (L : Set X))
    {x : X} (hx : x ∈ canon T L o) : s * x * s⁻¹ ∈ canon T L o := by
  refine Subgroup.mem_iInf.mpr fun W => Subgroup.mem_iInf.mpr fun hW => ?_
  obtain ⟨hTW, hWL, hWo⟩ := hW
  let W' : Subgroup X := W.comap (MulAut.conj s).toMonoidHom
  have hTW' : T ≤ W' := fun t ht => hTW ((Subgroup.mem_normalizer_iff.mp hsT t).mp ht)
  have hW'L : W' ≤ L := fun y hy => (Subgroup.mem_normalizer_iff.mp hsL y).mpr (hWL hy)
  have hW'o : Nat.card W' = o := by
    rw [← hWo]
    show Nat.card (W.comap (MulAut.conj s).toMonoidHom) = _
    rw [Subgroup.comap_equiv_eq_map_symm']
    exact Subgroup.card_map_of_injective (MulAut.conj s).symm.injective
  exact (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx W') ⟨hTW', hW'L, hW'o⟩ :)

theorem mem_normalizer_canon {T L : Subgroup X} {o : ℕ} {s : X}
    (hsT : s ∈ Subgroup.normalizer (T : Set X)) (hsL : s ∈ Subgroup.normalizer (L : Set X)) :
    s ∈ Subgroup.normalizer (canon T L o : Set X) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨conj_mem_canon hsT hsL, fun h => ?_⟩
  have := conj_mem_canon (Subgroup.inv_mem _ hsT) (Subgroup.inv_mem _ hsL) h
  simpa [mul_assoc] using this

theorem mem_normalizer_inf {A B : Subgroup X} {s : X}
    (hA : s ∈ Subgroup.normalizer (A : Set X)) (hB : s ∈ Subgroup.normalizer (B : Set X)) :
    s ∈ Subgroup.normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hA x,
    Subgroup.mem_normalizer_iff.mp hB x]

@[expose] def Key (T L : Subgroup X) : Prop :=
  ∀ W : Subgroup X, T ≤ W → W ≤ L → 5 ∣ Nat.card W → ∃ o₁ o₂ : ℕ,
    W ⊓ canon T L o₁ ≠ W ∧ W ⊓ canon T L o₂ ≠ W ∧
      (W ⊓ canon T L o₁) ⊔ (W ⊓ canon T L o₂) = W

theorem five_dvd_inf [Finite X] {L P : Subgroup X} [L.Normal] (hL2 : L.index ∣ 2)
    (h5 : 5 ∣ Nat.card P) : 5 ∣ Nat.card ↥(P ⊓ L) := by
  have h1 := Subgroup.card_mul_index (L.subgroupOf P)
  have h2 : (L.subgroupOf P).index ∣ 2 := (Subgroup.relIndex_dvd_index_of_normal L P).trans hL2
  have h3 : Nat.card (L.subgroupOf P) = Nat.card ↥(P ⊓ L) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h3] at h1
  have hcop : Nat.Coprime 5 (L.subgroupOf P).index :=
    Nat.Coprime.coprime_dvd_right h2 (by norm_num)
  exact hcop.dvd_of_dvd_mul_right (h1 ▸ h5)

theorem not_five_dvd [Finite X] {L S P : Subgroup X} [L.Normal] (hL2 : L.index ∣ 2)
    (hS : IsSylowTwoOf S ⊤) (hkey : Key (S ⊓ L) L) (hP : P ∈ uFam ⊤ S) :
    ¬ 5 ∣ Nat.card P := by
  intro h5
  have hLS := sup_eq_top hL2 hS
  have hSP : S ≤ P := hP.2.1.le
  have hTQ : S ⊓ L ≤ P ⊓ L := inf_le_inf_right L hSP
  obtain ⟨o₁, o₂, hne₁, hne₂, hsup⟩ := hkey (P ⊓ L) hTQ inf_le_right (five_dvd_inf hL2 h5)
  have hN : ∀ o, S ≤ Subgroup.normalizer (((P ⊓ L) ⊓ canon (S ⊓ L) L o : Subgroup X) : Set X) := by
    intro o s hs
    have hsL : s ∈ Subgroup.normalizer (L : Set X) := by
      rw [Subgroup.normalizer_eq_top]; trivial
    have hsS : s ∈ Subgroup.normalizer (S : Set X) := Subgroup.le_normalizer hs
    have hsP : s ∈ Subgroup.normalizer (P : Set X) := Subgroup.le_normalizer (hSP hs)
    exact mem_normalizer_inf (mem_normalizer_inf hsP hsL)
      (mem_normalizer_canon (mem_normalizer_inf hsS hsL) hsL)
  exact false_of_pair hP hLS inf_le_left inf_le_left (le_inf hTQ le_canon) (le_inf hTQ le_canon)
    (hN o₁) (hN o₂) hne₁ hne₂ hsup

structure Lat (T L : Subgroup X) (J : ℕ) (Z : ℕ → Subgroup X) : Prop where
  T_le : ∀ j < J, T ≤ Z j
  le_L : ∀ j < J, Z j ≤ L
  complete : ∀ W : Subgroup X, T ≤ W → W ≤ L → W = L ∨ ∃ j < J, W = Z j

namespace Lat

variable {T L : Subgroup X} {J : ℕ} {Z : ℕ → Subgroup X}

theorem sup_eq (h : Lat T L J Z) {a b : ℕ} (ha : a < J) {A B W : Subgroup X} (hA : Z a ≤ A)
    (hB : Z b ≤ B) (hAW : A ≤ W) (hBW : B ≤ W) (hWL : W ≤ L)
    (hW : ∀ j < J, Z a ≤ Z j → Z b ≤ Z j → W ≤ Z j) : A ⊔ B = W := by
  have hV : A ⊔ B ≤ W := sup_le hAW hBW
  rcases h.complete (A ⊔ B) ((h.T_le a ha).trans (hA.trans le_sup_left)) (hV.trans hWL) with
    hL | ⟨j, hj, hZ⟩
  · exact le_antisymm hV (hWL.trans hL.ge)
  · exact le_antisymm hV ((hW j hj (hZ ▸ hA.trans le_sup_left) (hZ ▸ hB.trans le_sup_right)).trans
      hZ.ge)

theorem le_canon (h : Lat T L J Z) {m o : ℕ} (hL : Nat.card L ≠ o)
    (hm : ∀ j < J, Nat.card (Z j) = o → Z m ≤ Z j) : Z m ≤ canon T L o := by
  refine le_canon_of fun W hTW hWL hWo => ?_
  rcases h.complete W hTW hWL with rfl | ⟨j, hj, rfl⟩
  · exact absurd hWo hL
  · exact hm j hj hWo

theorem case (h : Lat T L J Z) {W : Subgroup X} (hWL : W ≤ L) {o₁ o₂ a b m₁ m₂ : ℕ}
    (ha : a < J) (hm₁ : m₁ < J) (hm₂ : m₂ < J) (hL₁ : Nat.card L ≠ o₁) (hL₂ : Nat.card L ≠ o₂)
    (haW : Z a ≤ W) (hbW : Z b ≤ W) (ha₁ : ∀ j < J, Nat.card (Z j) = o₁ → Z a ≤ Z j)
    (hb₂ : ∀ j < J, Nat.card (Z j) = o₂ → Z b ≤ Z j) (hc₁ : Nat.card (Z m₁) = o₁)
    (hc₂ : Nat.card (Z m₂) = o₂) (hn₁ : ¬ W ≤ Z m₁) (hn₂ : ¬ W ≤ Z m₂)
    (hj : ∀ j < J, Z a ≤ Z j → Z b ≤ Z j → W ≤ Z j) :
    W ⊓ canon T L o₁ ≠ W ∧ W ⊓ canon T L o₂ ≠ W ∧
      (W ⊓ canon T L o₁) ⊔ (W ⊓ canon T L o₂) = W := by
  refine ⟨fun he => hn₁ ?_, fun he => hn₂ ?_, h.sup_eq ha (le_inf haW (h.le_canon hL₁ ha₁))
    (le_inf hbW (h.le_canon hL₂ hb₂)) inf_le_left inf_le_left hWL hj⟩
  · rw [← he]
    exact inf_le_right.trans (canon_le (h.T_le m₁ hm₁) (h.le_L m₁ hm₁) hc₁)
  · rw [← he]
    exact inf_le_right.trans (canon_le (h.T_le m₂ hm₂) (h.le_L m₂ hm₂) hc₂)

end Lat

theorem isSylowTwoOf_subgroupOf {L T : Subgroup X} (hT : IsSylowTwoOf T L) :
    IsSylowTwoOf (T.subgroupOf L) ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨?_, hT.2.2⟩
  exact hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm

theorem exists_lat {Γ : Type} [Group Γ] [Finite Γ] {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤)
    {J : ℕ} {Y : ℕ → Subgroup Γ} (hSY : ∀ j < J, S₀ ≤ Y j)
    (hall : ∀ Z : Subgroup Γ, S₀ ≤ Z → ∃ j ≤ J, Z = memberOrTop J Y j)
    {L T : Subgroup X} (hT : IsSylowTwoOf T L) (e : ↥L ≃* Γ) :
    ∃ φ : Γ →* X, Function.Injective φ ∧ Lat T L J (fun j => (Y j).map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥L := Finite.of_equiv Γ e.symm.toEquiv
  have hT' := isSylowTwoOf_map e (isSylowTwoOf_subgroupOf hT)
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT'
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S₀ = ((T.subgroupOf L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg
    exact this.symm
  let ψ : ↥L ≃* Γ := e.trans (MulAut.conj g)
  have hψ : (T.subgroupOf L).map ψ.toMonoidHom = S₀ := by
    rw [hST, Subgroup.map_map]
    rfl
  let φ : Γ →* X := L.subtype.comp ψ.symm.toMonoidHom
  have hφ : Function.Injective φ := L.subtype_injective.comp ψ.symm.injective
  have hrange : φ.range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hS₀T : S₀.map φ = T := by
    rw [← hψ, Subgroup.map_map]
    have : φ.comp ψ.toMonoidHom = L.subtype := by
      ext x
      simp [φ]
    rw [this, Subgroup.map_subgroupOf_eq_of_le hT.1]
  refine ⟨φ, hφ, ⟨fun j hj => hS₀T ▸ Subgroup.map_mono (hSY j hj),
    fun j _ => hrange ▸ Subgroup.map_le_range φ _, fun W hTW hWL => ?_⟩⟩
  have hS₀W : S₀ ≤ W.comap φ := Subgroup.map_le_iff_le_comap.mp (hS₀T ▸ hTW)
  have hWmap : (W.comap φ).map φ = W := Subgroup.map_comap_eq_self (hrange ▸ hWL)
  obtain ⟨j, hj, hZ⟩ := hall _ hS₀W
  by_cases hjJ : j < J
  · right
    refine ⟨j, hjJ, ?_⟩
    rw [← hWmap, hZ]
    simp [memberOrTop, hjJ]
  · left
    rw [← hWmap, hZ]
    simp only [memberOrTop, hjJ, ite_false]
    rw [← MonoidHom.range_eq_map, hrange]

end CFSG.Quasithin.H13.KGMinPar
