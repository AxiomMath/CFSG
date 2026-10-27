module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tg
public import CFSG.Quasithin.Vol2.Ch11SecAFactsLine

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin Ch11.SecA

section Fix

variable {W : Type*} [CommGroup W] [Finite W]

theorem exists_fix_mod (hW : ∀ w : W, w ^ 2 = 1) {S : Subgroup (MulAut W)} (hS : IsPGroup 2 ↥S)
    {M Z : Subgroup W} (hMS : ∀ s ∈ S, ∀ x ∈ M, s x ∈ M) (hZS : ∀ s ∈ S, ∀ z ∈ Z, s z ∈ Z)
    (hM : ¬ M ≤ Z) : ∃ v ∈ M, v ∉ Z ∧ ∀ s ∈ S, s v * v⁻¹ ∈ Z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M' := M ⊔ Z with hM'
  have hM'S : ∀ s ∈ S, ∀ x ∈ M', s x ∈ M' := by
    intro s hs x hx
    obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx
    rw [map_mul]
    exact M'.mul_mem (Subgroup.mem_sup_left (hMS s hs m hm))
      (Subgroup.mem_sup_right (hZS s hs z hz))
  let Z' : Subgroup ↥M' := Z.subgroupOf M'
  let act : ↥S → ↥M' →* ↥M' := fun s =>
    { toFun := fun x => ⟨(s : MulAut W) x, hM'S s s.2 x x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  have hact : ∀ s : ↥S, Z' ≤ Z'.comap (act s) := fun s x hx =>
    hZS s s.2 (x : W) hx
  let φ : ↥S → (↥M' ⧸ Z' →* ↥M' ⧸ Z') := fun s => QuotientGroup.map Z' Z' (act s) (hact s)
  have hφ : ∀ (s : ↥S) (x : ↥M'), φ s (QuotientGroup.mk x) = QuotientGroup.mk (act s x) :=
    fun s x => rfl
  let _ : MulAction ↥S (↥M' ⧸ Z') :=
    { smul := fun s q => φ s q
      one_smul := fun q => by
        induction q using QuotientGroup.induction_on with
        | H x => exact congrArg QuotientGroup.mk (Subtype.ext rfl)
      mul_smul := fun s t q => by
        induction q using QuotientGroup.induction_on with
        | H x => exact congrArg QuotientGroup.mk (Subtype.ext rfl) }
  have hQ2 : IsPGroup 2 (↥M' ⧸ Z') := fun q => by
    induction q using QuotientGroup.induction_on with
    | H x => exact ⟨1, by rw [pow_one, ← QuotientGroup.mk_pow,
        show x ^ 2 = 1 from Subtype.ext (hW x), QuotientGroup.mk_one]⟩
  obtain ⟨m₀, hm₀, hm₀Z⟩ := Set.not_subset.mp hM
  have hne : (QuotientGroup.mk (⟨m₀, Subgroup.mem_sup_left hm₀⟩ : ↥M') : ↥M' ⧸ Z') ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hm₀Z
  have hcard : 2 ∣ Nat.card (↥M' ⧸ Z') := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hQ2)
    rcases k with _ | k
    · exfalso
      rw [pow_zero] at hk
      exact hne (Finite.card_le_one_iff_subsingleton.mp hk.le |>.elim _ _)
    · rw [hk]
      exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  have h1 : (1 : ↥M' ⧸ Z') ∈ MulAction.fixedPoints ↥S (↥M' ⧸ Z') := fun s =>
    map_one (φ s)
  obtain ⟨b, hb, hb1⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hcard h1
  induction b using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨m, hm, z, hz, hmz⟩ := Subgroup.mem_sup.mp x.2
    have hxZ : (x : W) ∉ Z := fun h =>
      hb1 ((QuotientGroup.eq_one_iff (N := Z') x).mpr h).symm
    refine ⟨m, hm, fun hmZ => hxZ (hmz ▸ Z.mul_mem hmZ hz), fun s hs => ?_⟩
    have h2 := (QuotientGroup.eq_one_iff _).mp (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hφ, mul_inv_eq_one]
      exact hb ⟨s, hs⟩ : (QuotientGroup.mk (act ⟨s, hs⟩ x * x⁻¹) : ↥M' ⧸ Z') = 1)
    change s (x : W) * (x : W)⁻¹ ∈ Z at h2
    rw [← hmz, map_mul] at h2
    have h3 := Z.mul_mem h2 (Z.mul_mem (Z.inv_mem (hZS s hs z hz)) hz)
    have e : s m * s z * (m * z)⁻¹ * ((s z)⁻¹ * z) = s m * m⁻¹ := by
      rw [mul_inv_rev]
      have := mul_comm (s z) (z⁻¹ * m⁻¹)
      calc s m * s z * (z⁻¹ * m⁻¹) * ((s z)⁻¹ * z)
          = s m * (s z * (z⁻¹ * m⁻¹)) * ((s z)⁻¹ * z) := by rw [mul_assoc (s m)]
        _ = s m * (z⁻¹ * m⁻¹ * s z) * ((s z)⁻¹ * z) := by rw [this]
        _ = s m * (z⁻¹ * m⁻¹) * z := by group
        _ = s m * m⁻¹ := by rw [mul_comm z⁻¹ m⁻¹]; group
    rwa [e] at h3

end Fix

section Line

variable {W : Type} [CommGroup W] [Finite W] {H S : Subgroup (MulAut W)} {Z U₂ : Subgroup W}
  {q : ℕ}

omit [Finite W] in
theorem commS_le_line (U₂ : Subgroup W) {S₂ : Subgroup (MulAut W)} (hS₂ : S₂ ≤ stabW U₂) :
    commS S₂ U₂ ≤ U₂ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨s, hs, u, hu, rfl⟩
  exact U₂.mul_mem ((mem_stabW.mp (hS₂ hs) u).mp hu) (U₂.inv_mem hu)

theorem eq_commS_of_line (hW : ∀ w : W, w ^ 2 = 1) (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (hS : QuasithinUnique.IsSylowTwoOf S H) (hU₂ : IsFlagW H S Z q 2 U₂)
    (hLF : LineFacts H Z U₂) (hLT : LineTorusFacts H S Z U₂ q) {M : Subgroup W}
    (hMS : ∀ s ∈ S, ∀ x ∈ M, s x ∈ M)
    (hML : ∀ s ∈ perfectCore (H ⊓ stabW U₂), ∀ x ∈ M, s x ∈ M)
    (hMc : M ≤ commS (perfectCore (H ⊓ stabW U₂)) M)
    (hMcard : (fixV (perfectCore (H ⊓ stabW U₂)) ⊓ M).relIndex M ≤ q ^ 2) (hM : M ≠ ⊥) :
    M = commS (perfectCore (H ⊓ stabW U₂)) U₂ := by
  set S₂ := perfectCore (H ⊓ stabW U₂) with hS₂def
  set A₂ := commS S₂ U₂ with hA₂def
  obtain ⟨hZU, -, hidx, -⟩ := hU₂
  obtain ⟨-, -, hc, hd, -⟩ := hLF
  obtain ⟨hfix, hirr, -⟩ := hLT
  have hS₂H : ∀ s ∈ S₂, s ∈ H := fun s hs => (perfectCore_le _ hs).1
  have hS₂U : S₂ ≤ stabW U₂ := fun s hs => (perfectCore_le _ hs).2
  have hA₂U : A₂ ≤ U₂ := commS_le_line U₂ hS₂U
  have hMZ : ¬ M ≤ Z := by
    intro hMZ
    apply hM
    refine eq_bot_iff.mpr (le_trans hMc ((Subgroup.closure_le _).mpr ?_))
    rintro _ ⟨s, hs, m, hm, rfl⟩
    rw [hHZ s (hS₂H s hs) m (hMZ hm), mul_inv_cancel]
    exact Subgroup.one_mem _
  obtain ⟨v, hvM, hvZ, hvS⟩ := exists_fix_mod hW hS.2.1 hMS
    (fun s hs z hz => (hHZ s (hS.1 hs) z hz).symm ▸ hz) hMZ
  have hvU := hfix v hvS
  have hX : (M ⊓ U₂) ⊔ Z = U₂ := by
    refine (hirr _ le_sup_right (sup_le inf_le_right hZU) fun s hs x hx => ?_).resolve_left
      fun h => hvZ (h ▸ Subgroup.mem_sup_left ⟨hvM, hvU⟩)
    obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx
    rw [map_mul, hHZ s (hS₂H s hs) z hz]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hML s hs a ha.1,
      (mem_stabW.mp (hS₂U hs) a).mp ha.2⟩) (Subgroup.mem_sup_right hz)
  have hA₂M : A₂ ≤ M := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨s, hs, u, hu, rfl⟩
    rw [← hX] at hu
    obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
    have e : s (a * z) * (a * z)⁻¹ = s a * a⁻¹ := by
      rw [map_mul, hHZ s (hS₂H s hs) z hz, mul_inv_rev]
      group
    rw [e]
    exact M.mul_mem (hML s hs a ha.1) (M.inv_mem ha.1)
  set C := fixV S₂ ⊓ M with hC
  have hA₂C : C ⊓ A₂ ≤ Z := fun x hx =>
    (hc x (hA₂U hx.2)).mp fun s hs => hx.1.1 s hs
  have hq2 : Z.relIndex A₂ = q ^ 2 := by
    rw [← Subgroup.relIndex_sup_right, ← hd, hidx]
  have hfin : ∀ X Y : Subgroup W, X.relIndex Y ≠ 0 := fun X Y =>
    (Subgroup.index_ne_zero_of_finite : (X.subgroupOf Y).index ≠ 0)
  have hge : q ^ 2 ≤ C.relIndex A₂ := by
    rw [← hq2]
    calc Z.relIndex A₂ ≤ (C ⊓ A₂).relIndex A₂ := Subgroup.relIndex_le_of_le_left hA₂C (hfin _ _)
      _ = C.relIndex A₂ := Subgroup.inf_relIndex_right C A₂
  have hmul := Subgroup.relIndex_mul_relIndex C (A₂ ⊔ C) M le_sup_right
    (sup_le hA₂M inf_le_right)
  rw [Subgroup.relIndex_sup_right] at hmul
  have h1 : (A₂ ⊔ C).relIndex M = 1 := by
    have hpos : 0 < (A₂ ⊔ C).relIndex M := Nat.pos_of_ne_zero (hfin _ _)
    have hq0 : 0 < q ^ 2 := hidx ▸ Nat.pos_of_ne_zero (hfin _ _)
    have : C.relIndex A₂ * (A₂ ⊔ C).relIndex M ≤ q ^ 2 := hmul ▸ hMcard
    have h2 : q ^ 2 * (A₂ ⊔ C).relIndex M ≤ q ^ 2 * 1 :=
      le_trans (Nat.mul_le_mul_right _ hge) (by rw [mul_one]; exact this)
    have := Nat.le_of_mul_le_mul_left h2 hq0
    omega
  have hMA : M ≤ A₂ ⊔ C := Subgroup.relIndex_eq_one.mp h1
  refine le_antisymm (le_trans hMc ((Subgroup.closure_le _).mpr ?_)) hA₂M
  rintro _ ⟨s, hs, m, hm, rfl⟩
  obtain ⟨a, ha, c, hc', rfl⟩ := Subgroup.mem_sup.mp (hMA hm)
  have e : s (a * c) * (a * c)⁻¹ = s a * a⁻¹ := by
    rw [map_mul, hc'.1 s hs, mul_inv_rev]
    group
  rw [e]
  exact Subgroup.subset_closure ⟨s, hs, a, hA₂U ha, rfl⟩

omit [Finite W] in
theorem torus_of_line (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (hLF : LineFacts H Z U₂)
    (hLT : LineTorusFacts H S Z U₂ q) :
    ∃ t ∈ H, (∀ w ∈ commS (perfectCore (H ⊓ stabW U₂)) U₂,
        t w ∈ commS (perfectCore (H ⊓ stabW U₂)) U₂) ∧
      (∃ w ∈ commS (perfectCore (H ⊓ stabW U₂)) U₂, t w ≠ w) ∧
      (∀ ψ ∈ perfectCore (H ⊓ stabW U₂), ∀ w ∈ commS (perfectCore (H ⊓ stabW U₂)) U₂,
        (t * ψ * t⁻¹ * ψ⁻¹) w = w) ∧ t ^ (q - 1) = 1 := by
  set S₂ := perfectCore (H ⊓ stabW U₂) with hS₂def
  obtain ⟨ha, -, -, hd, -⟩ := hLF
  obtain ⟨-, -, t, htHU, htq, htc, u, hu, htu⟩ := hLT
  have hS₂U : S₂ ≤ stabW U₂ := fun s hs => (perfectCore_le _ hs).2
  have htN : t ∈ Subgroup.normalizer (S₂ : Set (MulAut W)) :=
    normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer htHU)
  refine ⟨t, htHU.1, fun w hw => ?_, ?_, fun ψ hψ w hw => ha _ (htc ψ hψ) w
    (commS_le_line U₂ hS₂U hw), htq⟩
  · induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨s, hs, v, hv, rfl⟩ := hx
      have e : t (s v * v⁻¹) = (t * s * t⁻¹) (t v) * (t v)⁻¹ := by
        simp [MulAut.mul_apply]
      rw [e]
      exact Subgroup.subset_closure ⟨_, (Subgroup.mem_normalizer_iff.mp htN s).mp hs, t v,
        (mem_stabW.mp htHU.2 v).mp hv, rfl⟩
    | one => simp
    | mul x y _ _ hx hy => simpa using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa using Subgroup.inv_mem _ hx
  · by_contra hcon
    push Not at hcon
    apply htu
    rw [hd] at hu
    obtain ⟨a, haA, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul, hcon a haA, hHZ t htHU.1 z hz]

end Line

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
