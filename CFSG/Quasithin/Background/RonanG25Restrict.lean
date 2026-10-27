module

public import CFSG.Quasithin.Background.RonanG25Defs

public section

namespace CFSG.Quasithin.RonanG25

section Restrict

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {X : Subgroup G}

theorem conj_mem_of_sup {H A M : Subgroup G} {c : G} (hH : ∀ h ∈ H, c * h * c⁻¹ ∈ M)
    (hA : ∀ a ∈ A, c * a * c⁻¹ ∈ M) {g : G} (hg : g ∈ H ⊔ A) : c * g * c⁻¹ ∈ M := by
  have key : H ⊔ A ≤ M.comap (MulAut.conj c).toMonoidHom :=
    sup_le (fun h hh => hH h hh) (fun a ha => hA a ha)
  exact key hg

theorem exists_mul_of_mem_sup {H A B : Subgroup G} (hHB : H ≤ B)
    (hA : ∀ y ∈ B, ∀ z ∈ A, y * z * y⁻¹ ∈ A) {g : G} (hg : g ∈ H ⊔ A) :
    ∃ h ∈ H, ∃ a ∈ A, h * a = g := by
  let S : Subgroup G :=
    { carrier := {g | ∃ h ∈ H, ∃ a ∈ A, h * a = g}
      one_mem' := ⟨1, H.one_mem, 1, A.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, a₁, ha₁, rfl⟩ ⟨h₂, hh₂, a₂, ha₂, rfl⟩
        have hc : h₂⁻¹ * a₁ * h₂ ∈ A := by
          have := hA h₂⁻¹ (B.inv_mem (hHB hh₂)) a₁ ha₁
          rwa [inv_inv] at this
        exact ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, (h₂⁻¹ * a₁ * h₂) * a₂, A.mul_mem hc ha₂, by group⟩
      inv_mem' := by
        rintro _ ⟨h, hh, a, ha, rfl⟩
        exact ⟨h⁻¹, H.inv_mem hh, h * a⁻¹ * h⁻¹, hA h (hHB hh) a⁻¹ (A.inv_mem ha), by group⟩ }
  have hS : H ⊔ A ≤ S :=
    sup_le (fun h hh => ⟨h, hh, 1, A.one_mem, mul_one h⟩)
      (fun a ha => ⟨1, H.one_mem, a, ha, one_mul a⟩)
  obtain ⟨h, hh, a, ha, hha⟩ := hS hg
  exact ⟨h, hh, a, ha, hha⟩

theorem normal_of_abelian {A M B : Subgroup G} (hAM : A ≤ M) (hMB : M ≤ B)
    (hab : ∀ y ∈ B, ∀ z ∈ B, y * z * y⁻¹ * z⁻¹ ∈ A) :
    ∀ y ∈ B, ∀ z ∈ M, y * z * y⁻¹ ∈ M := by
  intro y hy z hz
  have hu : z⁻¹ * y * z * y⁻¹ ∈ A := by
    have := hab z⁻¹ (B.inv_mem (hMB hz)) y hy
    rwa [inv_inv] at this
  have e : y * z * y⁻¹ = z * (z⁻¹ * y * z * y⁻¹) := by group
  rw [e]
  exact M.mul_mem hz (hAM hu)

theorem chief_hcl_of_abelian {A B : Subgroup G} (hs : ChiefStep X A B)
    (hab : ∀ y ∈ B, ∀ z ∈ B, y * z * y⁻¹ * z⁻¹ ∈ A) :
    ∀ M : Subgroup G, A ≤ M → M ≤ B → Inv X M → M = A ∨ M = B :=
  fun M hAM hMB hInvM => hs.simple M hAM hMB hInvM (normal_of_abelian hAM hMB hab)

theorem chief_hcl_of_prime [Finite G] {A B : Subgroup G} {p : ℕ} (hp : p.Prime) (hAB : A ≤ B)
    (hcard : Nat.card B = p * Nat.card A) :
    ∀ M : Subgroup G, A ≤ M → M ≤ B → M = A ∨ M = B := by
  intro M hAM hMB
  haveI : Nonempty A := ⟨1⟩
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hidx : A.relIndex B = p := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := B)
    rw [inf_eq_left.2 hAB, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right hApos h
  have hmul := Subgroup.relIndex_mul_relIndex A M B hAM hMB
  rw [hidx] at hmul
  rcases (Nat.dvd_prime hp).1 (⟨M.relIndex B, hmul.symm⟩ : A.relIndex M ∣ p) with h1 | h1
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.1 h1) hAM)
  · have h2 : M.relIndex B = 1 := by
      rw [h1] at hmul
      exact Nat.eq_of_mul_eq_mul_left hp.pos (hmul.trans (mul_one p).symm)
    exact Or.inr (le_antisymm hMB (Subgroup.relIndex_eq_one.1 h2))

theorem sup_inf_eq_of_chief {Q A B : Subgroup G} (hQ : Inv X Q) (hs : ChiefStep X A B)
    (hcl : ∀ M : Subgroup G, A ≤ M → M ≤ B → Inv X M → M = A ∨ M = B)
    {w : G} (hwQ : w ∈ Q) (hwB : w ∈ B) (hwA : w ∉ A) : (Q ⊓ B) ⊔ A = B := by
  have hAB : A ≤ B := hs.lt.le
  have hMB : (Q ⊓ B) ⊔ A ≤ B := sup_le inf_le_right hAB
  have hAM : A ≤ (Q ⊓ B) ⊔ A := le_sup_right
  have hInv : Inv X ((Q ⊓ B) ⊔ A) := by
    intro x hx g hg
    refine conj_mem_of_sup (H := Q ⊓ B) (A := A) (fun h hh => ?_) (fun a ha => ?_) hg
    · exact Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hQ x hx h (Subgroup.mem_inf.1 hh).1,
        hs.invB x hx h (Subgroup.mem_inf.1 hh).2⟩)
    · exact Subgroup.mem_sup_right (hs.invA x hx a ha)
  rcases hcl _ hAM hMB hInv with h1 | h1
  · have hwS : w ∈ (Q ⊓ B) ⊔ A := Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hwQ, hwB⟩)
    rw [h1] at hwS
    exact absurd hwS hwA
  · exact h1

theorem chiefStep_inf_of {Q A B : Subgroup G} (hQ : Inv X Q) (hs : ChiefStep X A B)
    (hcl : ∀ M : Subgroup G, A ≤ M → M ≤ B → Inv X M → M = A ∨ M = B)
    {w : G} (hwQ : w ∈ Q) (hwB : w ∈ B) (hwA : w ∉ A) : ChiefStep X (Q ⊓ A) (Q ⊓ B) := by
  have hAB : A ≤ B := hs.lt.le
  have hsup := sup_inf_eq_of_chief hQ hs hcl hwQ hwB hwA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne (le_inf inf_le_left ((inf_le_right : Q ⊓ A ≤ A).trans hAB))
      (fun heq => hwA ?_)
    have hmem : w ∈ Q ⊓ B := Subgroup.mem_inf.2 ⟨hwQ, hwB⟩
    rw [← heq] at hmem
    exact (Subgroup.mem_inf.1 hmem).2
  · intro x hx y hy
    exact Subgroup.mem_inf.2 ⟨hQ x hx y (Subgroup.mem_inf.1 hy).1,
      hs.invA x hx y (Subgroup.mem_inf.1 hy).2⟩
  · intro x hx y hy
    exact Subgroup.mem_inf.2 ⟨hQ x hx y (Subgroup.mem_inf.1 hy).1,
      hs.invB x hx y (Subgroup.mem_inf.1 hy).2⟩
  · intro y hy z hz
    exact Subgroup.mem_inf.2
      ⟨Q.mul_mem (Q.mul_mem (Subgroup.mem_inf.1 hy).1 (Subgroup.mem_inf.1 hz).1)
        (Q.inv_mem (Subgroup.mem_inf.1 hy).1),
        hs.normal y (Subgroup.mem_inf.1 hy).2 z (Subgroup.mem_inf.1 hz).2⟩
  · rintro Q' hN hH hInvQ' -
    have hQ'B : Q' ≤ B := (hH : Q' ≤ Q ⊓ B).trans inf_le_right
    have hInvM' : Inv X (Q' ⊔ A) := by
      intro x hx g hg
      refine conj_mem_of_sup (H := Q') (A := A) (fun h hh => ?_) (fun a ha => ?_) hg
      · exact Subgroup.mem_sup_left (hInvQ' x hx h hh)
      · exact Subgroup.mem_sup_right (hs.invA x hx a ha)
    rcases hcl (Q' ⊔ A) le_sup_right (sup_le hQ'B hAB) hInvM' with h1 | h1
    · left
      have hQ'A : Q' ≤ A := (le_sup_left : Q' ≤ Q' ⊔ A).trans h1.le
      exact le_antisymm (le_inf (hH.trans inf_le_left) hQ'A) hN
    · right
      refine le_antisymm hH ?_
      intro y hy
      have hyM : y ∈ Q' ⊔ A := by
        rw [h1]
        exact (Subgroup.mem_inf.1 hy).2
      obtain ⟨q, hq, a, ha, hqa⟩ := exists_mul_of_mem_sup hQ'B hs.normal hyM
      have hqQB := Subgroup.mem_inf.1 (hH hq)
      have haQ : a ∈ Q := by
        have ha_eq : a = q⁻¹ * y := by
          rw [← hqa, inv_mul_cancel_left]
        rw [ha_eq]
        exact Q.mul_mem (Q.inv_mem hqQB.1) (Subgroup.mem_inf.1 hy).1
      have ha' : a ∈ Q' := hN (Subgroup.mem_inf.2 ⟨haQ, ha⟩)
      rw [← hqa]
      exact Q'.mul_mem hq ha'

theorem card_eq_mul_of_sup [Finite G] {K A B : Subgroup G} (hKB : K ≤ B) (hAB : A ≤ B)
    (hA : ∀ y ∈ B, ∀ z ∈ A, y * z * y⁻¹ ∈ A) (hsup : K ⊔ A = B) {m : ℕ}
    (hcard : Nat.card B = m * Nat.card A) : Nat.card ↥K = m * Nat.card ↥(A ⊓ K) := by
  haveI : Nonempty A := ⟨1⟩
  have hApos : 0 < Nat.card A := Nat.card_pos
  haveI hN : (A.subgroupOf B).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (by
      have := hA (g : G) g.2 (n : G) (Subgroup.mem_subgroupOf.1 hn)
      simpa using this)⟩
  have htop : (K.subgroupOf B) ⊔ (A.subgroupOf B) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro b
    have hb : (b : G) ∈ K ⊔ A := by
      rw [hsup]
      exact b.2
    obtain ⟨k, hk, a, ha, hka⟩ := exists_mul_of_mem_sup hKB hA hb
    have hbeq : b = (⟨k, hKB hk⟩ : ↥B) * ⟨a, hAB ha⟩ := Subtype.ext hka.symm
    rw [hbeq]
    exact (K.subgroupOf B ⊔ A.subgroupOf B).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hk))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 ha))
  have h1 : (A.subgroupOf B).relIndex ((K.subgroupOf B) ⊔ (A.subgroupOf B)) =
      (A.subgroupOf B).relIndex (K.subgroupOf B) :=
    Subgroup.relIndex_sup_right (K.subgroupOf B) (A.subgroupOf B)
  rw [htop, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hKB] at h1
  have hidx : A.relIndex K = A.relIndex B := h1.symm
  have hK := Subgroup.relIndex_mul_card (H := A) (K := K)
  have hB := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [inf_eq_left.2 hAB, hcard] at hB
  have hm : A.relIndex B = m := Nat.eq_of_mul_eq_mul_right hApos hB
  rw [← hK, hidx, hm]

theorem card_restrict_eq [Finite G] {Q A B : Subgroup G} (hAB : A ≤ B)
    (hA : ∀ y ∈ B, ∀ z ∈ A, y * z * y⁻¹ ∈ A) (hsup : (Q ⊓ B) ⊔ A = B) {m : ℕ}
    (hcard : Nat.card B = m * Nat.card A) : Nat.card ↥(Q ⊓ B) = m * Nat.card ↥(Q ⊓ A) := by
  have hAK : A ⊓ (Q ⊓ B) = Q ⊓ A := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).2).1,
        (Subgroup.mem_inf.1 hx).1⟩
    · exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, Subgroup.mem_inf.2
        ⟨(Subgroup.mem_inf.1 hx).1, hAB (Subgroup.mem_inf.1 hx).2⟩⟩
  have h := card_eq_mul_of_sup (inf_le_right : Q ⊓ B ≤ B) hAB hA hsup hcard
  rw [hAK] at h
  exact h

theorem abelian_of_factorNatural {A B : Subgroup G} (hn : FactorNatural F X A B) :
    ∀ y ∈ B, ∀ z ∈ B, y * z * y⁻¹ * z⁻¹ ∈ A := by
  obtain ⟨φ, β, -, hφk, -, -, -⟩ := hn
  intro y hy z hz
  have hmem : y * z * y⁻¹ * z⁻¹ ∈ B :=
    B.mul_mem (B.mul_mem (B.mul_mem hy hz) (B.inv_mem hy)) (B.inv_mem hz)
  have key : φ (⟨y * z * y⁻¹ * z⁻¹, hmem⟩ : ↥B) = 1 := by
    have e : (⟨y * z * y⁻¹ * z⁻¹, hmem⟩ : ↥B) =
        (⟨y, hy⟩ : ↥B) * ⟨z, hz⟩ * (⟨y, hy⟩ : ↥B)⁻¹ * (⟨z, hz⟩ : ↥B)⁻¹ :=
      Subtype.ext (by simp)
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc : ∀ u v : Multiplicative (Fin 2 → F), u * v * u⁻¹ * v⁻¹ = 1 := by
      intro u v
      rw [mul_right_comm u v u⁻¹, mul_inv_cancel, one_mul, mul_inv_cancel]
    exact hc _ _
  exact (hφk _).1 key

theorem factorNatural_inf {A B Q : Subgroup G} (hAB : A ≤ B)
    (hA : ∀ y ∈ B, ∀ z ∈ A, y * z * y⁻¹ ∈ A) (hsup : (Q ⊓ B) ⊔ A = B)
    (hn : FactorNatural F X A B) : FactorNatural F X (Q ⊓ A) (Q ⊓ B) := by
  obtain ⟨φ, β, hφs, hφk, hφe, h2, h3⟩ := hn
  unfold FactorNatural
  refine ⟨φ.comp (Subgroup.inclusion (inf_le_right : Q ⊓ B ≤ B)), β, ?_, ?_, ?_, h2, h3⟩
  · intro w
    obtain ⟨y, hy⟩ := hφs w
    have hyS : (y : G) ∈ (Q ⊓ B) ⊔ A := by
      rw [hsup]
      exact y.2
    obtain ⟨q, hq, a, ha, hqa⟩ := exists_mul_of_mem_sup (inf_le_right : Q ⊓ B ≤ B) hA hyS
    have hqB : q ∈ B := (Subgroup.mem_inf.1 hq).2
    have haB : a ∈ B := hAB ha
    refine ⟨⟨q, hq⟩, ?_⟩
    show φ (⟨q, hqB⟩ : ↥B) = w
    have hya : y = (⟨q, hqB⟩ : ↥B) * (⟨a, haB⟩ : ↥B) := Subtype.ext hqa.symm
    have ha1 : φ (⟨a, haB⟩ : ↥B) = 1 := (hφk _).2 ha
    rw [← hy, hya, map_mul, ha1, mul_one]
  · intro k
    constructor
    · intro hk
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 k.2).1,
        (hφk (Subgroup.inclusion (inf_le_right : Q ⊓ B ≤ B) k)).1 hk⟩
    · intro hk
      exact (hφk (Subgroup.inclusion (inf_le_right : Q ⊓ B ≤ B) k)).2 (Subgroup.mem_inf.1 hk).2
  · intro x y y' hxy
    exact hφe x (Subgroup.inclusion (inf_le_right : Q ⊓ B ≤ B) y)
      (Subgroup.inclusion (inf_le_right : Q ⊓ B ≤ B) y') hxy

theorem ChainCounts.restrict [Finite G] {Q P : Subgroup G} (hQ : Inv X Q) (hP : Inv X P)
    (hcomm : ∀ x ∈ X, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Q) {A C : Subgroup G} {a b : ℕ}
    (h : ChainCounts F X false A C a b) (hCP : C ≤ P) :
    ChainCounts F X false (Q ⊓ A) (Q ⊓ C) a b := by
  revert hCP
  induction h with
  | refl A hA =>
    intro _
    refine ChainCounts.refl (Q ⊓ A) ?_
    intro x hx y hy
    exact Subgroup.mem_inf.2 ⟨hQ x hx y (Subgroup.mem_inf.1 hy).1, hA x hx y (Subgroup.mem_inf.1 hy).2⟩
  | @natural A B C a b hs hn rest ih =>
    intro hCP
    have hBP : B ≤ P := rest.le.trans hCP
    have hAB : A ≤ B := hs.lt.le
    obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ X, ∃ y ∈ B, x * y * x⁻¹ * y⁻¹ ∉ A := by
      have hnc := FactorNatural.not_central hAB hn
      unfold FactorCentral at hnc
      push Not at hnc
      exact hnc
    have hwQ : x * y * x⁻¹ * y⁻¹ ∈ Q := hcomm x hx y (hBP hy)
    have hwB : x * y * x⁻¹ * y⁻¹ ∈ B := B.mul_mem (hs.invB x hx y hy) (B.inv_mem hy)
    have hcl := chief_hcl_of_abelian hs (abelian_of_factorNatural hn)
    have hsup := sup_inf_eq_of_chief hQ hs hcl hwQ hwB hxy
    exact ChainCounts.natural (chiefStep_inf_of hQ hs hcl hwQ hwB hxy)
      (factorNatural_inf hAB hs.normal hsup hn) (ih hCP)
  | @additional A B C a b hs habel hc hcard rest ih =>
    intro hCP
    have hBP : B ≤ P := rest.le.trans hCP
    have hAB : A ≤ B := hs.lt.le
    obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ X, ∃ y ∈ B, x * y * x⁻¹ * y⁻¹ ∉ A := by
      unfold FactorCentral at hc
      push Not at hc
      exact hc
    have hwQ : x * y * x⁻¹ * y⁻¹ ∈ Q := hcomm x hx y (hBP hy)
    have hwB : x * y * x⁻¹ * y⁻¹ ∈ B := B.mul_mem (hs.invB x hx y hy) (B.inv_mem hy)
    have hcl := chief_hcl_of_abelian hs habel
    have hsup := sup_inf_eq_of_chief hQ hs hcl hwQ hwB hxy
    have habel' : ∀ u ∈ Q ⊓ B, ∀ v ∈ Q ⊓ B, u * v * u⁻¹ * v⁻¹ ∈ Q ⊓ A := by
      intro u hu v hv
      have hu' := Subgroup.mem_inf.1 hu
      have hv' := Subgroup.mem_inf.1 hv
      exact Subgroup.mem_inf.2
        ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem hu'.1 hv'.1) (Q.inv_mem hu'.1)) (Q.inv_mem hv'.1),
          habel u hu'.2 v hv'.2⟩
    have hnc' : ¬ FactorCentral X (Q ⊓ A) (Q ⊓ B) := by
      intro hcen
      obtain ⟨k, hk, a', ha', hka⟩ := exists_mul_of_mem_sup (inf_le_right : Q ⊓ B ≤ B) hs.normal
        (show y ∈ (Q ⊓ B) ⊔ A by rw [hsup]; exact hy)
      have hkB : k ∈ B := (Subgroup.mem_inf.1 hk).2
      have hck : x * k * x⁻¹ * k⁻¹ ∈ A := (Subgroup.mem_inf.1 (hcen x hx k hk)).2
      apply hxy
      rw [← hka]
      have e : x * (k * a') * x⁻¹ * (k * a')⁻¹ =
          (x * k * x⁻¹ * k⁻¹) * (k * (x * a' * x⁻¹ * a'⁻¹) * k⁻¹) := by group
      rw [e]
      exact A.mul_mem hck (hs.normal k hkB _ (A.mul_mem (hs.invA x hx a' ha') (A.inv_mem ha')))
    have hcard' := card_restrict_eq hAB hs.normal hsup hcard
    exact ChainCounts.additional (chiefStep_inf_of hQ hs hcl hwQ hwB hxy) habel' hnc' hcard'
      (ih hCP)
  | @central A B C a b hs hc p hp hcard rest ih =>
    intro hCP
    have hBP : B ≤ P := rest.le.trans hCP
    have hAB : A ≤ B := hs.lt.le
    by_cases hdead : Q ⊓ B ≤ A
    · have heq : Q ⊓ A = Q ⊓ B :=
        le_antisymm (le_inf inf_le_left (inf_le_right.trans hAB)) (le_inf inf_le_left hdead)
      have hih := ih hCP
      rw [← heq] at hih
      exact hih
    · have hex : ∃ w ∈ Q ⊓ B, w ∉ A := by
        by_contra hcon
        exact hdead (fun w hw => by
          by_contra hwA
          exact hcon ⟨w, hw, hwA⟩)
      obtain ⟨w, hwS, hwA⟩ := hex
      have hwQ : w ∈ Q := (Subgroup.mem_inf.1 hwS).1
      have hwB : w ∈ B := (Subgroup.mem_inf.1 hwS).2
      have hcl : ∀ M : Subgroup G, A ≤ M → M ≤ B → Inv X M → M = A ∨ M = B :=
        fun M hAM hMB _ => chief_hcl_of_prime hp hAB hcard M hAM hMB
      have hsup := sup_inf_eq_of_chief hQ hs hcl hwQ hwB hwA
      have hc' : FactorCentral X (Q ⊓ A) (Q ⊓ B) := by
        intro x hx k hk
        exact Subgroup.mem_inf.2 ⟨hcomm x hx k (hBP (Subgroup.mem_inf.1 hk).2),
          hc x hx k (Subgroup.mem_inf.1 hk).2⟩
      have hcard' := card_restrict_eq hAB hs.normal hsup hcard
      exact ChainCounts.central (chiefStep_inf_of hQ hs hcl hwQ hwB hwA) hc' hp hcard' (ih hCP)
  | @other A B C a b hord hs h2 rest ih =>
    exact absurd hord Bool.false_ne_true

end Restrict

end CFSG.Quasithin.RonanG25
