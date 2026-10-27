module

public import CFSG.Quasithin.Background.F420Basic
public import CFSG.Quasithin.Background.G6PGroup
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Quasithin CFSG.QuasithinUnique

namespace FFL

@[expose] def FixesFixed (D : FFModel) (T : Subgroup D.Gam) (γ : D.Gam) : Prop :=
  ∀ m ∈ D.sec, (∀ τ ∈ T, D.act τ m * m⁻¹ ∈ D.ker) → D.act γ m * m⁻¹ ∈ D.ker

variable {V : Type} [CommGroup V]

theorem mul_inv_mem_of_fixesFixed {D : FFModel} {H : Subgroup (MulAut V)} {I Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H I Z π) {T : Subgroup D.Gam} {γ : D.Gam}
    (hD : FixesFixed D T γ) {v : V} (hv : v ∈ I)
    (hfix : ∀ τ ∈ T, ((π τ : ↥H) : MulAut V) v = v) :
    ((π γ : ↥H) : MulAut V) v * v⁻¹ ∈ Z := by
  obtain ⟨-, -, -, hinvI, -, hsec, -, β, -, hβk, hβe⟩ := h
  set u : ↥I := ⟨v, hv⟩ with hu
  obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (β u)
  have hfix' : ∀ τ ∈ T, D.act τ (m₀ : D.Amb) * (m₀ : D.Amb)⁻¹ ∈ D.ker := by
    intro τ hτ
    have h1 := hβe τ u m₀ (hinvI _ v hv) (hsec τ _ m₀.2) hm₀.symm
    have h2 : (⟨((π τ : ↥H) : MulAut V) (u : V), hinvI _ v hv⟩ : ↥I) = u :=
      Subtype.ext (hfix τ hτ)
    rw [h2, ← hm₀] at h1
    have h3 := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at h3
    rw [mul_comm]
    exact h3
  have hγ := hD _ m₀.2 hfix'
  have h1 := hβe γ u m₀ (hinvI _ v hv) (hsec γ _ m₀.2) hm₀.symm
  have h4 : β ⟨((π γ : ↥H) : MulAut V) (u : V), hinvI _ v hv⟩ = β u := by
    rw [h1, ← hm₀]
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    change (D.act γ (m₀ : D.Amb))⁻¹ * (m₀ : D.Amb) ∈ D.ker
    rw [show (D.act γ (m₀ : D.Amb))⁻¹ * (m₀ : D.Amb) =
      (D.act γ (m₀ : D.Amb) * (m₀ : D.Amb)⁻¹)⁻¹ by rw [mul_inv_rev, inv_inv, mul_comm]]
    exact D.ker.inv_mem hγ
  have h5 : β (⟨((π γ : ↥H) : MulAut V) (u : V), hinvI _ v hv⟩ * u⁻¹) = 1 := by
    rw [map_mul, map_inv, h4, mul_inv_cancel]
  exact (hβk _).mp h5

theorem ne_one_of_realizesVia {D : FFModel} {H : Subgroup (MulAut V)} {I Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H I Z π) {γ : D.Gam} {m : D.Amb} (hm : m ∈ D.sec)
    (hγ : D.act γ m * m⁻¹ ∉ D.ker) : π γ ≠ 1 := by
  intro h1
  obtain ⟨-, -, -, hinvI, -, hsec, -, β, hβs, -, hβe⟩ := h
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
  have h2 := hβe γ u ⟨m, hm⟩ (hinvI _ u u.2) (hsec γ m hm) hu
  have h3 : (⟨((π γ : ↥H) : MulAut V) (u : V), hinvI _ u u.2⟩ : ↥I) = u :=
    Subtype.ext (by rw [h1]; rfl)
  rw [h3, hu] at h2
  have h4 := QuotientGroup.eq.mp h2
  rw [Subgroup.mem_subgroupOf] at h4
  apply hγ
  rw [mul_comm]
  exact h4

theorem eq_of_mul_inv_mem (hV : ∀ v : V, v * v = 1) {g : MulAut V} (hg : g ^ 3 = 1)
    {Z : Subgroup V} (hZ : ∀ z ∈ Z, g z = z) {v : V} (hv : g v * v⁻¹ ∈ Z) : g v = v := by
  obtain ⟨z, hzZ, hgv⟩ : ∃ z ∈ Z, g v = z * v := ⟨_, hv, by rw [inv_mul_cancel_right]⟩
  have hgz : g z = z := hZ z hzZ
  have e1 : g (g v) = z * (z * v) := by rw [hgv, map_mul, hgz, hgv]
  have e2 : g (g (g v)) = z * (z * (z * v)) := by rw [e1, map_mul, map_mul, hgz, hgv]
  have h3 : g (g (g v)) = v := by
    have : (g ^ 3) v = v := by rw [hg]; rfl
    simpa [pow_succ, MulAut.mul_apply] using this
  have hzz : z * z = 1 := hV z
  rw [e2, ← mul_assoc, hzz, one_mul] at h3
  have hz1 : z = 1 := by simpa using h3
  rw [hgv, hz1, one_mul]

theorem fix_of_sup {I₁ I₂ : Subgroup V} (hind : I₁ ⊓ I₂ = ⊥) {T : Set (MulAut V)}
    {g : MulAut V} (hT₁ : ∀ t ∈ T, ∀ v ∈ I₁, t v ∈ I₁) (hT₂ : ∀ t ∈ T, ∀ v ∈ I₂, t v ∈ I₂)
    (h₁ : ∀ v ∈ I₁, (∀ t ∈ T, t v = v) → g v = v)
    (h₂ : ∀ v ∈ I₂, (∀ t ∈ T, t v = v) → g v = v) :
    ∀ v ∈ I₁ ⊔ I₂, (∀ t ∈ T, t v = v) → g v = v := by
  intro v hv hfix
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
  have hab : ∀ t ∈ T, t a = a ∧ t b = b := by
    intro t ht
    have h1 : t a * t b = a * b := by rw [← map_mul, hfix t ht]
    have h2 : t a * a⁻¹ = b * (t b)⁻¹ :=
      calc t a * a⁻¹ = (t a * t b) * (a⁻¹ * (t b)⁻¹) := by
            rw [mul_mul_mul_comm, mul_inv_cancel (t b), mul_one]
        _ = (a * b) * (a⁻¹ * (t b)⁻¹) := by rw [h1]
        _ = b * (t b)⁻¹ := by rw [mul_mul_mul_comm, mul_inv_cancel a, one_mul]
    have hmem : t a * a⁻¹ ∈ I₁ ⊓ I₂ :=
      ⟨I₁.mul_mem (hT₁ t ht a ha) (I₁.inv_mem ha),
        h2 ▸ I₂.mul_mem hb (I₂.inv_mem (hT₂ t ht b hb))⟩
    rw [hind, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    refine ⟨hmem, ?_⟩
    rw [hmem] at h1
    exact mul_left_cancel h1
  rw [map_mul, h₁ a ha fun t ht => (hab t ht).1, h₂ b hb fun t ht => (hab t ht).2]

theorem apply_mem_iSup {ι : Type*} {I : ι → Subgroup V} {t : MulAut V} (p : ι → Prop)
    (hT : ∀ i, p i → ∀ v ∈ I i, t v ∈ I i) {v : V} (hv : v ∈ ⨆ (i) (_ : p i), I i) :
    t v ∈ ⨆ (i) (_ : p i), I i := by
  have hle : (⨆ (i) (_ : p i), I i) ≤ (⨆ (i) (_ : p i), I i).comap t.toMonoidHom := by
    refine iSup₂_le fun i hi => ?_
    intro w hw
    exact (le_iSup₂ (f := fun i (_ : p i) => I i) i hi) (hT i hi w hw)
  exact hle hv

theorem fix_of_iSup_finset {ι : Type*} [DecidableEq ι] (I : ι → Subgroup V)
    (hind : ∀ i, I i ⊓ ⨆ (j) (_ : j ≠ i), I j = ⊥) {T : Set (MulAut V)} {g : MulAut V}
    (hT : ∀ t ∈ T, ∀ i, ∀ v ∈ I i, t v ∈ I i)
    (h : ∀ i, ∀ v ∈ I i, (∀ t ∈ T, t v = v) → g v = v) (s : Finset ι) :
    ∀ v ∈ ⨆ i ∈ s, I i, (∀ t ∈ T, t v = v) → g v = v := by
  induction s using Finset.induction_on with
  | empty =>
    intro v hv _
    simp only [Finset.notMem_empty, iSup_of_empty, iSup_bot, Subgroup.mem_bot] at hv
    rw [hv, map_one]
  | insert a s has ih =>
    have hsplit : (⨆ i ∈ insert a s, I i) = I a ⊔ ⨆ i ∈ s, I i := Finset.iSup_insert a s I
    rw [hsplit]
    refine fix_of_sup ?_ (fun t ht v hv => hT t ht a v hv) (fun t ht v hv => ?_) (h a) ih
    · refine le_bot_iff.mp (le_trans (inf_le_inf_left _ ?_) (hind a).le)
      refine iSup₂_le fun i hi => ?_
      exact le_iSup₂_of_le (f := fun (j : ι) (_ : j ≠ a) => I j) i
        (fun e => has (e ▸ hi)) le_rfl
    · exact apply_mem_iSup (fun i => i ∈ s) (fun i _ w hw => hT t ht i w hw) hv

theorem fix_of_iSup {ι : Type*} [Fintype ι] [DecidableEq ι] (I : ι → Subgroup V)
    (hind : ∀ i, I i ⊓ ⨆ (j) (_ : j ≠ i), I j = ⊥) {T : Set (MulAut V)} {g : MulAut V}
    (hT : ∀ t ∈ T, ∀ i, ∀ v ∈ I i, t v ∈ I i)
    (h : ∀ i, ∀ v ∈ I i, (∀ t ∈ T, t v = v) → g v = v) :
    ∀ v ∈ ⨆ i, I i, (∀ t ∈ T, t v = v) → g v = v := by
  intro v hv
  have : (⨆ i, I i) = ⨆ i ∈ (Finset.univ : Finset ι), I i := by simp
  rw [this] at hv
  exact fix_of_iSup_finset I hind hT h _ v hv

theorem exists_fix_of_isSylowTwoOf [Finite V] {L S T : Subgroup (MulAut V)} {U : Subgroup V}
    {g : MulAut V} (hS : IsSylowTwoOf S L) (hTL : T ≤ L) (hT : IsPGroup 2 T) (hgL : g ∈ L)
    (hg : orderOf g = 3) (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U)
    (hfix : ∀ v ∈ U, (∀ t ∈ T, t v = v) → g v = v) :
    ∃ g' ∈ L, orderOf g' = 3 ∧ ∀ v ∈ fixV S ⊓ U, g' v = v := by
  have hT' : IsPGroup 2 (T.subgroupOf L) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  have hS' : CFSG.Open.quasithinIsSylowTwo (S.subgroupOf L) :=
    ⟨hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, hS.2.2⟩
  obtain ⟨h, hh⟩ := F420.exists_conj_mem_of_isPGroup hT' hS'
  refine ⟨(h : MulAut V) * g * (h : MulAut V)⁻¹,
    L.mul_mem (L.mul_mem h.2 hgL) (L.inv_mem h.2), ?_, ?_⟩
  · rw [show (h : MulAut V) * g * (h : MulAut V)⁻¹ = MulAut.conj (h : MulAut V) g from rfl,
      MulEquiv.orderOf_eq, hg]
  · rintro v ⟨hvS, hvU⟩
    have hw : (h : MulAut V)⁻¹ v ∈ U := hU _ (L.inv_mem h.2) v hvU
    have hwT : ∀ t ∈ T, t ((h : MulAut V)⁻¹ v) = (h : MulAut V)⁻¹ v := by
      intro t ht
      have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ T.subgroupOf L := ht
      have h2 := hh _ h1
      rw [Subgroup.mem_subgroupOf] at h2
      have h3 := (mem_fixV.mp hvS) _ h2
      have h4 : t ((h : MulAut V)⁻¹ v) =
          (h : MulAut V)⁻¹ (((h * ⟨t, hTL ht⟩ * h⁻¹ : ↥L) : MulAut V) v) := by
        simp [MulAut.mul_apply]
      rw [h4, h3]
    have hgw := hfix _ hw hwT
    change (h : MulAut V) (g ((h : MulAut V)⁻¹ v)) = v
    rw [hgw]
    simp

theorem exists_fix_of_hom [Finite V] {L S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S L)
    {Γ : Type*} [Group Γ] (ψ : Γ →* MulAut V) (hψ : ∀ x, ψ x ∈ L) {T₀ : Subgroup Γ}
    (hT₀ : IsPGroup 2 T₀) {γ : Γ} (hγ : orderOf (ψ γ) = 3)
    (hfix : ∀ v ∈ commV L, (∀ τ ∈ T₀, ψ τ v = v) → ψ γ v = v) :
    ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v := by
  refine exists_fix_of_isSylowTwoOf hS (T := T₀.map ψ) ?_ (hT₀.map ψ) (hψ γ) hγ ?_ ?_
  · rintro _ ⟨τ, -, rfl⟩
    exact hψ τ
  · intro l hl u hu
    exact G6.apply_mem_commV (fun x hx => L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)) hu
  · intro v hv hT
    exact hfix v hv fun τ hτ => hT _ ⟨τ, hτ, rfl⟩

theorem exists_fix_of_realizesVia [Finite V] (hV : ∀ v : V, v * v = 1)
    {L S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S L) {D : FFModel} {π : D.Gam →* ↥L}
    (hπ : D.RealizesVia L (commV L) (fixV L ⊓ commV L) π) {T₀ : Subgroup D.Gam}
    (hT₀ : IsPGroup 2 T₀) {γ : D.Gam} (hγ3 : γ ^ 3 = 1) (hγ1 : π γ ≠ 1)
    (hD : FixesFixed D T₀ γ) :
    ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v := by
  have hg3 : (L.subtype.comp π γ) ^ 3 = 1 := by rw [← map_pow, hγ3, map_one]
  have hg1 : L.subtype.comp π γ ≠ 1 := fun h => hγ1 (Subtype.ext h)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine exists_fix_of_hom hS (L.subtype.comp π) (fun x => (π x).2) hT₀
    (orderOf_eq_prime hg3 hg1) fun v hv hT => ?_
  have h1 := mul_inv_mem_of_fixesFixed hπ hD hv hT
  exact eq_of_mul_inv_mem hV hg3
    (fun z (hz : z ∈ fixV L ⊓ commV L) => (mem_fixV.mp hz.1) _ (π γ).2) h1

end FFL

end CFSG.Quasithin.EmptyFaithfulMultiple
