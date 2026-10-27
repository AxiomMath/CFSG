module

public import CFSG.Quasithin.Background.F918D5

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

section Decomposition

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem d321i_exists_prod_of_mem_iSup (I : ι → Subgroup W) {x : W} (hx : x ∈ ⨆ i, I i) :
    ∃ y : ι → W, (∀ i, y i ∈ I i) ∧ x = ∏ i, y i := by
  refine Subgroup.iSup_induction I
    (C := fun x => ∃ y : ι → W, (∀ i, y i ∈ I i) ∧ x = ∏ i, y i) hx ?_ ?_ ?_
  · intro i x hx
    refine ⟨Pi.mulSingle i x, fun j => ?_, by simp⟩
    by_cases h : j = i
    · subst h
      simpa using hx
    · simp [Pi.mulSingle_eq_of_ne h]
  · exact ⟨fun _ => 1, fun i => (I i).one_mem, by simp⟩
  · rintro x x' ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨fun i => y i * y' i, fun i => (I i).mul_mem (hy i) (hy' i),
      by simp [Finset.prod_mul_distrib]⟩

theorem d321i_mem_of_mem_all {Z U : Subgroup W} (I : ι → Subgroup W)
    (hind : ∀ i, I i ⊓ (Z ⊔ ⨆ (j : ι) (_ : j ≠ i), I j) = Z)
    (hsum : Z ⊔ ⨆ i, I i = U) {v : W} (hvU : v ∈ U)
    (hv : ∀ i, v ∈ Z ⊔ ⨆ (j : ι) (_ : j ≠ i), I j) : v ∈ Z := by
  rw [← hsum] at hvU
  obtain ⟨z, hz, x, hx, rfl⟩ := Subgroup.mem_sup.1 hvU
  obtain ⟨y, hy, rfl⟩ := d321i_exists_prod_of_mem_iSup I hx
  refine Z.mul_mem hz (Z.prod_mem fun i _ => ?_)
  have hxP : ∏ j, y j ∈ Z ⊔ ⨆ (j : ι) (_ : j ≠ i), I j := by
    have h1 := (Z ⊔ ⨆ (j : ι) (_ : j ≠ i), I j).mul_mem
      ((Z ⊔ ⨆ (j : ι) (_ : j ≠ i), I j).inv_mem (Subgroup.mem_sup_left hz)) (hv i)
    simpa using h1
  have hrest : ∏ j ∈ Finset.univ.erase i, y j ∈ Z ⊔ ⨆ (j : ι) (_ : j ≠ i), I j := by
    refine Subgroup.prod_mem _ fun j hj => ?_
    exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem j
      (Subgroup.mem_iSup_of_mem (Finset.ne_of_mem_erase hj) (hy j)))
  have hyi : y i ∈ Z ⊔ ⨆ (j : ι) (_ : j ≠ i), I j := by
    have e : y i = (∏ j, y j) * (∏ j ∈ Finset.univ.erase i, y j)⁻¹ := by
      rw [← Finset.mul_prod_erase Finset.univ y (Finset.mem_univ i)]
      simp
    rw [e]
    exact Subgroup.mul_mem _ hxP (Subgroup.inv_mem _ hrest)
  rw [← hind i]
  exact ⟨hy i, hyi⟩

end Decomposition

section Transport

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}

theorem d321i_realizesVia_of_secIsoL {D : FFModel} {π : D.Gam →* ↥L} {I Z I' Z' : Subgroup W}
    (h : D.RealizesVia L I' Z' π) (hiso : SecIsoL L I Z I' Z') : D.RealizesVia L I Z π := by
  obtain ⟨hπs, -, hks, hinv', -, hsec, hker, β, hβs, hβk, hβe⟩ := h
  obtain ⟨hZI, -, hinv, hinvZ, -, -, β', hβ's, hβ'k, hβ'e⟩ := B5.secIsoL_iff.1 hiso
  let β₀ : ↥I' ⧸ Z'.subgroupOf I' →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    QuotientGroup.lift (Z'.subgroupOf I') β
      (fun u hu => (hβk u).2 (Subgroup.mem_subgroupOf.1 hu))
  have hβ₀ : ∀ u : ↥I', β₀ (QuotientGroup.mk u) = β u := fun u => rfl
  have hβ₀inj : ∀ x, β₀ x = 1 → x = 1 := by
    intro x hx
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hβ₀] at hx
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 ((hβk u).1 hx))
  refine ⟨hπs, hZI, hks, hinv, hinvZ, hsec, hker, β₀.comp β', ?_, ?_, ?_⟩
  · intro y
    obtain ⟨u, rfl⟩ := hβs y
    obtain ⟨v, hv⟩ := hβ's (QuotientGroup.mk u)
    exact ⟨v, by rw [MonoidHom.comp_apply, hv, hβ₀]⟩
  · intro v
    rw [MonoidHom.comp_apply, ← hβ'k v]
    exact ⟨hβ₀inj _, fun h1 => by rw [h1, map_one]⟩
  · intro γ u m hu hm hum
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β' u)
    have hx' : β x = QuotientGroup.mk m := by
      rw [← hβ₀, hx]
      exact hum
    have hπx : ((π γ : ↥L) : MulAut W) (x : W) ∈ I' := hinv' (π γ) x x.2
    have h1 := hβ'e (π γ) u x hu hπx hx.symm
    have h2 := hβe γ x m hπx hm hx'
    show β₀ (β' ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩) = _
    rw [h1, hβ₀]
    exact h2

end Transport

section Schur

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}

theorem d321i_projSec {A B Z S : Subgroup W}
    (hA : ∀ l ∈ L, ∀ w ∈ A, l w ∈ A) (hB : ∀ l ∈ L, ∀ w ∈ B, l w ∈ B)
    (hZ : ∀ l ∈ L, ∀ w ∈ Z, l w ∈ Z) (hS : S ≤ A ⊔ B) (hAB : A ⊓ B ≤ Z) :
    ∃ β : ↥S →* ↥A ⧸ Z.subgroupOf A,
      (∀ (s : ↥S) (a : ↥A) (b : W), b ∈ B → (s : W) = a * b → β s = QuotientGroup.mk a) ∧
      (∀ (γ : ↥L) (u : ↥S) (m : ↥A) (hu : (γ : MulAut W) (u : W) ∈ S)
        (hm : (γ : MulAut W) (m : W) ∈ A),
        β u = QuotientGroup.mk m →
          β ⟨(γ : MulAut W) (u : W), hu⟩ = QuotientGroup.mk ⟨(γ : MulAut W) (m : W), hm⟩) ∧
      ∀ s : ↥S, β s = 1 → (s : W) ∈ Z ⊔ B := by
  obtain ⟨β, hβ⟩ := exists_projSec_hom hS hAB
  refine ⟨β, hβ, ?_, ?_⟩
  · intro γ u m hu hm hum
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hS u.2)
    have h1 : β u = QuotientGroup.mk ⟨a, ha⟩ := hβ u ⟨a, ha⟩ b hb hab.symm
    have h2 : β ⟨(γ : MulAut W) (u : W), hu⟩ =
        QuotientGroup.mk ⟨(γ : MulAut W) a, hA γ γ.2 a ha⟩ := by
      refine hβ _ _ ((γ : MulAut W) b) (hB γ γ.2 b hb) ?_
      show (γ : MulAut W) (u : W) = (γ : MulAut W) a * (γ : MulAut W) b
      rw [← hab, map_mul]
    rw [h2]
    rw [h1, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hum
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h3 := hZ γ γ.2 _ hum
    simpa [map_mul, map_inv] using h3
  · intro s hs
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hS s.2)
    have h1 := hβ s ⟨a, ha⟩ b hb hab.symm
    rw [hs, eq_comm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    rw [← hab]
    exact Subgroup.mul_mem_sup h1 hb

theorem d321i_exists_secIsoL {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥L} {k : ℕ}
    {I : Fin k → Subgroup W} {U Z V : Subgroup W}
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 K)).RealizesVia L (I i) Z π)
    (hZinv : ∀ l ∈ L, ∀ z ∈ Z, l z ∈ Z)
    (hind : ∀ i, I i ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) = Z)
    (hsum : Z ⊔ ⨆ i, I i = U) (hVU : V ≤ U) (hVinv : ∀ l ∈ L, ∀ v ∈ V, l v ∈ V)
    (hVZ : ¬ V ≤ Z)
    (hVirr : ∀ X : Subgroup W, X ≤ V → (∀ l ∈ L, ∀ x ∈ X, l x ∈ X) → V ⊓ Z ≤ X →
      X = V ⊓ Z ∨ X = V) :
    ∃ i, SecIsoL L V (V ⊓ Z) (I i) Z := by
  have hIinv : ∀ i, ∀ l ∈ L, ∀ w ∈ I i, l w ∈ I i := fun i l hl w hw =>
    (hreal i).2.2.2.1 ⟨l, hl⟩ w hw
  have hPinv : ∀ i, ∀ l ∈ L, ∀ w ∈ Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j,
      l w ∈ Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j := by
    intro i
    have h1 : XMod.IsInv ↥L (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) :=
      XMod.IsInv.sup (fun a v hv => hZinv a a.2 v hv)
        (XMod.isInv_iSup fun j => XMod.isInv_iSup fun _ => fun a v hv => hIinv j a a.2 v hv)
    exact fun l hl w hw => h1 ⟨l, hl⟩ w hw
  obtain ⟨i, hi⟩ : ∃ i, V ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) = V ⊓ Z := by
    by_contra hcon
    push Not at hcon
    refine hVZ fun v hv => d321i_mem_of_mem_all I hind hsum (hVU hv) fun i => ?_
    rcases hVirr (V ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j)) inf_le_left
      (fun l hl x hx => ⟨hVinv l hl x hx.1, hPinv i l hl x hx.2⟩)
      (le_inf inf_le_left (inf_le_right.trans le_sup_left)) with h | h
    · exact absurd h (hcon i)
    · have hv' : v ∈ V ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) := by
        rw [h]
        exact hv
      exact hv'.2
  have hVle : V ≤ I i ⊔ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) := by
    refine hVU.trans ?_
    rw [← hsum]
    refine sup_le (le_sup_of_le_right le_sup_left) (iSup_le fun j => ?_)
    by_cases hji : j = i
    · subst hji
      exact le_sup_left
    · exact le_sup_of_le_right (le_sup_of_le_right (le_iSup₂_of_le j hji le_rfl))
  obtain ⟨β, hβdef, hβe, hβk⟩ := d321i_projSec (hIinv i) (hPinv i) hZinv hVle (hind i).le
  have hker : ∀ s : ↥V, β s = 1 ↔ (s : W) ∈ V ⊓ Z := by
    intro s
    constructor
    · intro hs
      have h1 := hβk s hs
      have h2 : (s : W) ∈ Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j := by
        rw [← sup_assoc, sup_idem] at h1
        exact h1
      have h3 : (s : W) ∈ V ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) := ⟨s.2, h2⟩
      rwa [hi] at h3
    · intro hs
      have h1 := hβdef s 1 (s : W) (Subgroup.mem_sup_left hs.2) (by simp)
      rwa [QuotientGroup.mk_one] at h1
  obtain ⟨ε, hε⟩ := exists_sec_equiv_nat (StatedSL 3 K) (hreal i)
  let φ : ↥V →* Multiplicative (Fin 3 → K) := ε.toMonoidHom.comp β
  have hJ : ∀ γ : ↥(StatedSL 3 K), ∀ x ∈ φ.range, natAct (StatedSL 3 K) γ x ∈ φ.range := by
    rintro γ _ ⟨v, rfl⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β v)
    have hπv : ((π γ : ↥L) : MulAut W) (v : W) ∈ V := hVinv _ (π γ).2 v v.2
    have hπm : ((π γ : ↥L) : MulAut W) (m : W) ∈ I i := hIinv i _ (π γ).2 m m.2
    have h1 := hβe (π γ) v m hπv hπm hm.symm
    refine ⟨⟨_, hπv⟩, ?_⟩
    show ε (β ⟨_, hπv⟩) = natAct (StatedSL 3 K) γ (ε (β v))
    rw [h1, ← hm]
    exact hε γ m hπm
  rcases B5.natural_invariant_eq (by norm_num : 2 ≤ 3) φ.range hJ with h0 | htop
  · exfalso
    refine hVZ fun v hv => ?_
    have hφ : φ ⟨v, hv⟩ = 1 := by
      have h1 : φ ⟨v, hv⟩ ∈ φ.range := ⟨_, rfl⟩
      rw [h0] at h1
      exact h1
    have hβ1 : β ⟨v, hv⟩ = 1 := ε.injective (hφ.trans (map_one ε).symm)
    exact ((hker ⟨v, hv⟩).1 hβ1).2
  · have hsurj : Function.Surjective β := by
      intro y
      have h1 : ε y ∈ φ.range := by
        rw [htop]
        trivial
      obtain ⟨v, hv⟩ := h1
      exact ⟨v, ε.injective hv⟩
    exact ⟨i, B5.secIsoL_iff.2 ⟨inf_le_left, (hreal i).2.1, fun h u hu => hVinv h h.2 u hu,
      fun h z hz => ⟨hVinv h h.2 z hz.1, hZinv h h.2 z hz.2⟩, (hreal i).2.2.2.1,
      fun h z hz => hZinv h h.2 z hz, β, hsurj, hker, hβe⟩⟩

end Schur

end CFSG.Quasithin
