module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKCoord
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKLinB
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKLinE
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKTrans
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBV

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

@[expose] def subgroupToSubmodule {n : ℕ} (B : AddSubgroup (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := B
  add_mem' := fun ha hb => B.add_mem ha hb
  zero_mem' := B.zero_mem
  smul_mem' := by
    intro c x hx
    have : c = 0 ∨ c = 1 := by revert c; decide
    rcases this with rfl | rfl
    · simpa using B.zero_mem
    · simpa using hx

theorem mem_subgroupToSubmodule {n : ℕ} (B : AddSubgroup (Fin n → ZMod 2)) (x : Fin n → ZMod 2) :
    x ∈ subgroupToSubmodule B ↔ x ∈ B := Iff.rfl

theorem finrank_subgroupToSubmodule {n m : ℕ} (B : AddSubgroup (Fin n → ZMod 2))
    (h : Nat.card B = 2 ^ m) : Module.finrank (ZMod 2) (subgroupToSubmodule B) = m := by
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(subgroupToSubmodule B))
  have h1 : Nat.card (subgroupToSubmodule B) = Nat.card B := rfl
  rw [h1, h, Nat.card_zmod] at h2
  exact (Nat.pow_right_injective (le_refl 2) h2).symm

theorem card_range_of_injective {n m : ℕ} (Φ : (Fin m → ZMod 2) →+ (Fin n → ZMod 2))
    (hΦ : Function.Injective Φ) : Nat.card Φ.range = 2 ^ m := by
  have hinj : Function.Injective Φ.rangeRestrict := fun a b h => hΦ (congrArg Subtype.val h)
  have hsurj := AddMonoidHom.rangeRestrict_surjective Φ
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)]
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card,
    Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]

theorem card_coordSet {n m j : ℕ} (B : AddSubgroup (Fin n → ZMod 2)) (h : Nat.card B = 2 ^ m) :
    Nat.card {t : Fin j → Fin n → ZMod 2 // ∀ i, t i ∈ B} = 2 ^ (m * j) := by
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun _ x => x ∈ B))]
  rw [Nat.card_fun, h, Nat.card_eq_fintype_card (α := Fin j), Fintype.card_fin, ← pow_mul]


variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k : ℕ}

theorem exists_std_coordinates (hN31 : NotC31)
    (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hd : NoSumBigData G T M L Mm I H K m k) {n j : ℕ}
    (hnm : (n = 4 ∧ m = 3) ∨ (n = 5 ∧ m = 3) ∨ (n = 5 ∧ m = 4))
    (α : ↥K →* GL (Fin n) (ZMod 2)) (β : ↥(uZero I K) →* Multiplicative (Fin j → Fin n → ZMod 2))
    (hsurj : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) (hbij : Function.Bijective β)
    (hequi : ∀ (x : ↥K) (u v : ↥(uZero I K)), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
      Multiplicative.toAdd (β v) i =
        ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
          (Multiplicative.toAdd (β u) i)) :
    ∃ (α' : ↥K →* GL (Fin n) (ZMod 2))
      (β' : ↥(uZero I K) →* Multiplicative (Fin j → Fin n → ZMod 2)),
      Function.Surjective α' ∧ α'.ker = CFSG.pCore 2 ↥K ∧ Function.Bijective β' ∧
      (∀ (x : ↥K) (u v : ↥(uZero I K)), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
        Multiplicative.toAdd (β' v) i =
          ((α' x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
            (Multiplicative.toAdd (β' u) i)) ∧
      (∀ v : ↥(uZero I K), (v : G) ∈ vV T L → ∀ (i : Fin j) (b : Fin n), m ≤ b.val →
        Multiplicative.toAdd (β' v) i b = 0) ∧
      (∀ x : Fin n → ZMod 2, (∀ b : Fin n, m ≤ b.val → x b = 0) →
        ∃ v : ↥(uZero I K), (v : G) ∈ vV T L ∧ ∃ i : Fin j, Multiplicative.toAdd (β' v) i = x) ∧
      k ≤ j ∧
      (j = k → ∀ z : ↥(uZero I K),
        (∀ (i : Fin j) (b : Fin n), m ≤ b.val → Multiplicative.toAdd (β' z) i b = 0) →
          (z : G) ∈ vV T L) := by
  classical
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  have hVU := vV_le_uZero hN31 h22 h27 hd
  obtain ⟨-, -, -, hm34, hmk, -, -, hsum⟩ := id hd
  have hm2 : 2 ≤ m := by rcases hm34 with h | h <;> omega
  have hn2m : n < 2 * m := by rcases hnm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hk0 : 0 < k := by omega
  have hAnorm : perfectCore (L ⊓ H) ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (vV T L : Set G) := by
    obtain ⟨_, _, _, hA, _⟩ := id hsum
    exact hA
  have hnormL : perfectCore (L ⊓ H) ≤ Subgroup.normalizer (vV T L : Set G) :=
    le_sup_left.trans hAnorm
  have hcardV : Nat.card (vV T L) = 2 ^ (m * k) := card_V_of_isSum hsum
  obtain ⟨ρ, βV, hρs, hβVb, hβVe⟩ := V_coords_of_isSum hc hsum
  let eV : ↥(vV T L) ≃* Multiplicative (Fin k → Fin m → ZMod 2) :=
    MulEquiv.ofBijective βV hβVb
  let incl : ↥(vV T L) →* ↥(uZero I K) := Subgroup.inclusion hVU
  let θ : Multiplicative (Fin k → Fin m → ZMod 2) →* Multiplicative (Fin j → Fin n → ZMod 2) :=
    β.comp (incl.comp eV.symm.toMonoidHom)
  let ϑ : (Fin k → Fin m → ZMod 2) →+ (Fin j → Fin n → ZMod 2) :=
    AddMonoidHom.mk' (fun t => Multiplicative.toAdd (θ (Multiplicative.ofAdd t)))
      (fun a b => by simp [ofAdd_add, map_mul, toAdd_mul])
  have hϑ : ∀ t, ϑ t = Multiplicative.toAdd (β (incl (eV.symm (Multiplicative.ofAdd t)))) :=
    fun t => rfl
  have hϑinj : Function.Injective ϑ := by
    intro t t' h
    have h1 : β (incl (eV.symm (Multiplicative.ofAdd t))) =
        β (incl (eV.symm (Multiplicative.ofAdd t'))) := by
      apply Multiplicative.toAdd.injective
      exact h
    have h2 := hbij.1 h1
    have h3 : eV.symm (Multiplicative.ofAdd t) = eV.symm (Multiplicative.ofAdd t') :=
      Subgroup.inclusion_injective hVU h2
    exact Multiplicative.ofAdd.injective (eV.symm.injective h3)
  let σ : ↥(perfectCore (L ⊓ H)) →* GL (Fin n) (ZMod 2) :=
    α.comp (Subgroup.inclusion hc.LH_le)
  have hϑequi : ∀ (γ : ↥(perfectCore (L ⊓ H))) (t : Fin k → Fin m → ZMod 2) (i : Fin j),
      ϑ (fun s => ((ρ γ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (t s)) i =
        ((σ γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (ϑ t i) := by
    intro γ t i
    set u : ↥(vV T L) := eV.symm (Multiplicative.ofAdd t) with hu
    have hmem : (γ : G) * (u : G) * (γ : G)⁻¹ ∈ vV T L :=
      (Subgroup.mem_normalizer_iff.mp (hnormL γ.2) (u : G)).mp u.2
    set v : ↥(vV T L) := ⟨(γ : G) * (u : G) * (γ : G)⁻¹, hmem⟩ with hv
    have hvγ : (v : G) = (γ : G) * (u : G) * (γ : G)⁻¹ := rfl
    have hβu : βV u = Multiplicative.ofAdd t := by
      have : eV u = Multiplicative.ofAdd t := by
        rw [hu]
        exact eV.apply_symm_apply _
      exact this
    have hβv : βV v = Multiplicative.ofAdd (fun s =>
        ((ρ γ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (t s)) := by
      apply Multiplicative.toAdd.injective
      funext s
      rw [hβVe γ u v hvγ s, hβu]
      rfl
    have hvu : v = eV.symm (Multiplicative.ofAdd (fun s =>
        ((ρ γ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (t s))) := by
      rw [MulEquiv.eq_symm_apply]
      exact hβv
    rw [hϑ, hϑ, ← hvu]
    have h := hequi ⟨(γ : G), hc.LH_le γ.2⟩ (incl u) (incl v) hvγ i
    exact h
  obtain ⟨Φ₀, i₀, s₀, hΦinj, hΦ₀, hΦA⟩ :=
    natural_sum_embedding hm2 hn2m hk0 ρ hρs σ ϑ hϑinj hϑequi
  set A₀ : AddSubgroup (Fin n → ZMod 2) := Φ₀.range with hA₀
  have hA₀card : Nat.card A₀ = 2 ^ m := card_range_of_injective Φ₀ hΦinj
  have hArank : Module.finrank (ZMod 2) (subgroupToSubmodule A₀) = m :=
    finrank_subgroupToSubmodule A₀ hA₀card
  obtain ⟨P, hP⟩ := exists_gl_std_of_finrank (subgroupToSubmodule A₀) hArank
  obtain ⟨α', β', hs', hk', hb', he', hβ'⟩ := transport_coordinates α β hsurj hker hbij hequi P
  have hVcoord : ∀ v₀ : ↥(vV T L), ∀ i : Fin j,
      Multiplicative.toAdd (β (incl v₀)) i ∈ A₀ := by
    intro v₀ i
    have h1 : eV.symm (eV v₀) = v₀ := eV.symm_apply_apply v₀
    have h2 := hΦA (Multiplicative.toAdd (eV v₀)) i
    rw [hϑ] at h2
    have h3 : Multiplicative.ofAdd (Multiplicative.toAdd (eV v₀)) = eV v₀ := rfl
    rw [h3, h1] at h2
    exact h2
  let g : ↥(vV T L) → {z : ↥(uZero I K) // ∀ i, Multiplicative.toAdd (β z) i ∈ A₀} :=
    fun v₀ => ⟨incl v₀, hVcoord v₀⟩
  have hginj : Function.Injective g := by
    intro a b h
    exact Subgroup.inclusion_injective hVU (congrArg Subtype.val h)
  have hcardS : Nat.card {z : ↥(uZero I K) // ∀ i, Multiplicative.toAdd (β z) i ∈ A₀} =
      2 ^ (m * j) := by
    rw [← card_coordSet (j := j) A₀ hA₀card]
    refine Nat.card_congr ((Equiv.subtypeEquiv (MulEquiv.ofBijective β hbij).toEquiv
      (q := fun t : Multiplicative (Fin j → Fin n → ZMod 2) =>
        ∀ i, Multiplicative.toAdd t i ∈ A₀) (fun z => Iff.rfl)).trans
      (Equiv.subtypeEquiv Multiplicative.toAdd (fun _ => Iff.rfl)))
  have hle : 2 ^ (m * k) ≤ 2 ^ (m * j) := by
    rw [← hcardV, ← hcardS]
    exact Nat.card_le_card_of_injective g hginj
  have hkj : k ≤ j := by
    have h1 : m * k ≤ m * j := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hVeq : j = k → ∀ z : ↥(uZero I K),
      (∀ (i : Fin j) (b : Fin n), m ≤ b.val → Multiplicative.toAdd (β' z) i b = 0) →
        (z : G) ∈ vV T L := by
    intro hjk z hz
    have hzS : ∀ i, Multiplicative.toAdd (β z) i ∈ A₀ := by
      intro i
      have : Multiplicative.toAdd (β z) i ∈ subgroupToSubmodule A₀ := by
        rw [hP]
        intro b hb
        rw [← hβ' z i]
        exact hz i b hb
      exact (mem_subgroupToSubmodule A₀ _).mp this
    have hbijg : Function.Bijective g :=
      (Nat.bijective_iff_injective_and_card g).mpr ⟨hginj, by rw [hcardV, hcardS, hjk]⟩
    obtain ⟨v₀, hv₀⟩ := hbijg.2 ⟨z, hzS⟩
    have : (incl v₀ : ↥(uZero I K)) = z := congrArg Subtype.val hv₀
    rw [← this]
    exact v₀.2
  refine ⟨α', β', hs', hk', hb', he', ?_, ?_, hkj, hVeq⟩
  · intro v hv i b hb
    have hmem : Multiplicative.toAdd (β v) i ∈ A₀ := hVcoord ⟨(v : G), hv⟩ i
    have h1 := (hP (Multiplicative.toAdd (β v) i)).mp hmem b hb
    rw [hβ' v i]
    exact h1
  · intro x hx
    set y : Fin n → ZMod 2 := ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec x
      with hy
    have hPy : (P : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec y = x := by
      rw [hy, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    have hyA : y ∈ subgroupToSubmodule A₀ := by
      rw [hP y]
      intro b hb
      rw [hPy]
      exact hx b hb
    obtain ⟨z, hz⟩ := (mem_subgroupToSubmodule A₀ y).mp hyA
    refine ⟨incl (eV.symm (Multiplicative.ofAdd (Pi.single s₀ z))), ?_, i₀, ?_⟩
    · exact (eV.symm (Multiplicative.ofAdd (Pi.single s₀ z))).2
    · rw [hβ', ← hϑ, hΦ₀, hz, hPy]

end CFSG.Quasithin.H13.Ch4.NSB
