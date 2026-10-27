module

public import CFSG.Quasithin.MS93.ASIrr
public import CFSG.Quasithin.MS93.ASIrrHeart
public import CFSG.Quasithin.EmptyFaithful.LRed6Hat
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueHatA6
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_le_of_relIndex_two {L A K : Subgroup G}
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) (hLK : L ≤ Subgroup.normalizer (K : Set G))
    (h2 : K.relIndex A = 2) : ⁅A, L⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha l hl
  have hc : l * a * l⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hLA hl) a).mp ha
  have hiff : l * a * l⁻¹ ∈ K ↔ a ∈ K := ((Subgroup.mem_normalizer_iff.mp (hLK hl) a)).symm
  have h2' : (K.subgroupOf A).index = 2 := h2
  have key := (Subgroup.mul_mem_iff_of_index_two h2' (a := ⟨a, ha⟩)
    (b := ⟨(l * a * l⁻¹)⁻¹, A.inv_mem hc⟩)).2 (by
      simp only [Subgroup.mem_subgroupOf]
      rw [K.inv_mem_iff, hiff])
  rw [Subgroup.mem_subgroupOf] at key
  simpa [commutatorElement_def, mul_assoc] using key

theorem eq_or_eq_of_relIndex_eight [Finite G] {L U C W : Subgroup G} (hCW : C ≤ W) (hWU : W ≤ U)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hLC : L ≤ Subgroup.normalizer (C : Set G)) (hU : ⁅U, L⁆ = U) (hW : ⁅W, L⁆ ⊔ C = W)
    (h8 : C.relIndex U = 8) : W = C ∨ W = U := by
  have hmul := Subgroup.relIndex_mul_relIndex C W U hCW hWU
  rw [h8] at hmul
  have h1 : C.relIndex W ≠ 2 := fun h2 => by
    have hWC : W ≤ C := hW ▸ sup_le (commutator_le_of_relIndex_two hLW hLC h2) le_rfl
    rw [Subgroup.relIndex_eq_one.mpr hWC] at h2
    exact absurd h2 (by norm_num)
  have h2 : W.relIndex U ≠ 2 := fun h2 => by
    have hle : ⁅U, L⁆ ≤ W := commutator_le_of_relIndex_two hLU hLW h2
    rw [hU] at hle
    rw [Subgroup.relIndex_eq_one.mpr hle] at h2
    exact absurd h2 (by norm_num)
  have hd : C.relIndex W ∣ 8 := Dvd.intro _ hmul
  have hle8 : C.relIndex W ≤ 8 := Nat.le_of_dvd (by norm_num) hd
  generalize hr : C.relIndex W = r at hmul hd hle8 h1
  generalize hs : W.relIndex U = s at hmul h2
  have hcases : r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 8 := by
    interval_cases r <;> omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp hr) hCW)
  · exact (h1 rfl).elim
  · exact (h2 (by omega)).elim
  · exact Or.inr (le_antisymm hWU (Subgroup.relIndex_eq_one.mp (hs.trans (by omega))))

theorem relIndex_eq_of_natural {A U C : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥A →* ↥Γ} {k : ℕ}
    {dual : Bool} (h : IsSumOfNaturalModulesVia A U C α dual k) :
    C.relIndex U = Nat.card (Fin k → ι → F) := by
  obtain ⟨-, -, β, hβ, hker, -⟩ := h
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hβ,
    Subgroup.card_top]
  rfl

theorem relIndex_eq_eight_of_natural_sl3_two {A U C : Subgroup G}
    {α : ↥A →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))}
    (h : IsSumOfNaturalModulesVia A U C α false 1) : C.relIndex U = 8 := by
  rw [relIndex_eq_of_natural h, Nat.card_eq_fintype_card]
  rfl

theorem eq_or_eq_of_altNaturalSection_six {L U C : Subgroup G} {N : Subgroup ↥L}
    (h : IsAltNaturalSection L U C N 6) {W : Subgroup G} (hCW : C ≤ W) (hWU : W ≤ U)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : W = C ∨ W = U := by
  obtain ⟨hLU, α, hα, -, β, -, hβker, hβeq⟩ := h
  let act : ↥L → Multiplicative (AltHeart 6) → Multiplicative (AltHeart 6) :=
    fun ℓ y => Multiplicative.ofAdd
      (SBc9.heartAct ((α ℓ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))
        (Multiplicative.toAdd y))
  have hact : ∀ (ℓ : ↥L) (u v : ↥U), (v : G) = ℓ * u * ℓ⁻¹ → β v = act ℓ (β u) := by
    intro ℓ u v huv
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β u))
    have he := hβeq ℓ u v huv x hx
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd (β v) = SBc9.heartAct _ (Multiplicative.toAdd (β u))
    rw [← hx, SBc9.heartAct_mk, he]
  have hirr : ∀ Y : Subgroup (Multiplicative (AltHeart 6)),
      (∀ (ℓ : ↥L) (y : Multiplicative (AltHeart 6)), y ∈ Y → act ℓ y ∈ Y) → Y = ⊥ ∨ Y = ⊤ := by
    intro Y hY
    let Ya : AddSubgroup (AltHeart 6) :=
      { carrier := {a | Multiplicative.ofAdd a ∈ Y}
        add_mem' := fun {a b} ha hb => by
          show Multiplicative.ofAdd (a + b) ∈ Y
          rw [ofAdd_add]
          exact Y.mul_mem ha hb
        zero_mem' := by
          show Multiplicative.ofAdd (0 : AltHeart 6) ∈ Y
          rw [ofAdd_zero]
          exact Y.one_mem
        neg_mem' := fun {a} ha => by
          show Multiplicative.ofAdd (-a) ∈ Y
          rw [ofAdd_neg]
          exact Y.inv_mem ha }
    have hYa : ∀ σ ∈ alternatingGroup (Fin 6), ∀ y ∈ Ya, SBc9.heartAct σ y ∈ Ya := by
      intro σ hσ y hy
      obtain ⟨ℓ, hℓ⟩ := hα ⟨σ, hσ⟩
      have := hY ℓ _ hy
      show Multiplicative.ofAdd (SBc9.heartAct σ y) ∈ Y
      have e : (((α ℓ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))) = σ := by
        rw [hℓ]
      rw [← e]
      exact this
    rcases heart6_irreducible Ya hYa with hb | ht
    · left
      refine eq_bot_iff.mpr fun y hy => ?_
      have : Multiplicative.toAdd y ∈ Ya := hy
      rw [hb, AddSubgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact this
    · right
      refine eq_top_iff.mpr fun y _ => ?_
      have : Multiplicative.toAdd y ∈ Ya := ht ▸ AddSubgroup.mem_top _
      exact this
  exact eq_or_eq_of_section β hβker act hact hirr hLU hCW hWU hLW

theorem eq_bot_or_eq_of_tripleA6Six [Finite G] {L U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hperf : ⁅L, L⁆ = L)
    (h6 : TripleA6Six (autI hU L) ⊤ ⊥) {W : Subgroup G} (hWU : W ≤ U)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = U := by
  have hcard : Nat.card (IntMod U hU) = 2 ^ 6 := (LRed6.hat_conclusion h6).2
  have hHhat : IsHat ↥(autI hU L) ↥(alternatingGroup (Fin 6)) := by
    obtain ⟨K, hK, hKf, Γ₀, -, -, hhat, -, π, hπ⟩ := h6
    have hinj : Function.Injective π :=
      FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
    exact IsHat.of_mulEquiv (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩) hhat
  have hp : Group.IsPerfect ↥(autI hU L) := by
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
    rw [← range_convHom hU L hLU]
    exact Group.IsPerfect.range _
  obtain ⟨-, hirr⟩ := H13.hatA6SixIrreducible (IntMod U hU) IntMod.sq_eq_one hcard
    (autI hU L) hp hHhat.2.1 hHhat.2.2
  exact eq_bot_or_eq_of_autI hU hirr hWU hLW

section G2

open CFSG.Quasithin.H13.Orbit CFSG.Quasithin.H.Mathieu

theorem zornQ_g2Derived_transitive {K : Type} [Field K] [Finite K] (hK2 : Nat.card K = 2) :
    ∀ m ∈ (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec,
      ∀ m' ∈ (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec,
        m ∉ (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).ker →
        m' ∉ (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).ker →
        ∃ γ : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Gam,
          ∃ k ∈ (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).ker,
            (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).act γ m = m' * k := by
  classical
  intro m hm m' hm' hmk hmk'
  obtain ⟨x, rfl⟩ : ∃ x : quasithinZorn K, Multiplicative.ofAdd x = m :=
    ⟨Multiplicative.toAdd m, rfl⟩
  obtain ⟨x', rfl⟩ : ∃ x : quasithinZorn K, Multiplicative.ofAdd x = m' :=
    ⟨Multiplicative.toAdd m', rfl⟩
  have hx : x.1 + x.2.2.2 = 0 := hm
  have hx' : x'.1 + x'.2.2.2 = 0 := hm'
  have hx0 : x ≠ 0 := fun h => hmk (by rw [h]; exact ⟨0, rfl⟩)
  have hx1 : x ≠ zornOne := fun h => hmk (by rw [h]; exact ⟨1, rfl⟩)
  have hx0' : x' ≠ 0 := fun h => hmk' (by rw [h]; exact ⟨0, rfl⟩)
  have hx1' : x' ≠ zornOne := fun h => hmk' (by rw [h]; exact ⟨1, rfl⟩)
  by_cases hc : zornClsD x = zornClsD x'
  · obtain ⟨γ, hγ, hγm⟩ := exists_g2Derived_of_cls hK2 hx hx' hc
    refine ⟨⟨γ, hγ⟩, 1, Subgroup.one_mem _, ?_⟩
    change Multiplicative.ofAdd (γ x) = Multiplicative.ofAdd x' * 1
    rw [mul_one, hγm]
  · have hc' := zornClsD_add_one_eq hK2 hx' hx0' hx1' hx0 hx1 hc
    obtain ⟨γ, hγ, hγm⟩ := exists_g2Derived_of_cls hK2 hx (zornOne_add_mem hK2 hx') hc'
    refine ⟨⟨γ, hγ⟩, Multiplicative.ofAdd zornOne, ⟨1, rfl⟩, ?_⟩
    change Multiplicative.ofAdd (γ x) = Multiplicative.ofAdd x' * Multiplicative.ofAdd zornOne
    rw [hγm]
    rfl

theorem eq_or_eq_of_realizesBy {V : Type*} [CommGroup V] {D : FFModel} {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : D.Gam →* ↥H} {β : ↥U →* ↥D.sec ⧸ D.ker.subgroupOf D.sec}
    (hR : RealizesBy D H U Z π β)
    (htrans : ∀ m ∈ D.sec, ∀ m' ∈ D.sec, m ∉ D.ker → m' ∉ D.ker →
      ∃ γ : D.Gam, ∃ k ∈ D.ker, D.act γ m = m' * k)
    {Y : Subgroup V} (hZY : Z ≤ Y) (hYU : Y ≤ U)
    (hY : ∀ h ∈ H, ∀ y ∈ Y, (h : MulAut V) y ∈ Y) : Y = Z ∨ Y = U := by
  obtain ⟨-, -, -, hHU, -, hsec, -, -, hβ1, hβeq⟩ := hR
  by_cases hYZ : Y ≤ Z
  · exact Or.inl (le_antisymm hYZ hZY)
  right
  obtain ⟨u, huY, huZ⟩ := Set.not_subset.mp hYZ
  refine le_antisymm hYU fun w hwU => ?_
  by_cases hwZ : w ∈ Z
  · exact hZY hwZ
  have huU : u ∈ U := hYU huY
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, huU⟩)
  obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective (β ⟨w, hwU⟩)
  have hnot : ∀ (v : ↥U) (n : ↥D.sec), (QuotientGroup.mk n : ↥D.sec ⧸ D.ker.subgroupOf D.sec) =
      β v → (v : V) ∉ Z → (n : D.Amb) ∉ D.ker := by
    intro v n hn hvZ hnk
    apply hvZ
    rw [← hβ1, ← hn, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hnk
  obtain ⟨γ, k, hk, he⟩ := htrans m m.2 m' m'.2 (hnot _ m hm huZ) (hnot _ m' hm' hwZ)
  have hu' : ((π γ : ↥H) : MulAut V) u ∈ U := hHU (π γ) u huU
  have hm2 : D.act γ (m : D.Amb) ∈ D.sec := hsec γ m m.2
  have h1 := hβeq γ ⟨u, huU⟩ m hu' hm2 hm.symm
  have h2 : β ⟨_, hu'⟩ = β ⟨w, hwU⟩ := by
    rw [h1, ← hm']
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    change (D.act γ m)⁻¹ * (m' : D.Amb) ∈ D.ker
    rw [he, mul_inv_rev, inv_mul_cancel_right]
    exact D.ker.inv_mem hk
  have h3 : β (⟨_, hu'⟩ * (⟨w, hwU⟩ : ↥U)⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
  have h4 : ((π γ : ↥H) : MulAut V) u * w⁻¹ ∈ Z := (hβ1 _).1 h3
  have h5 : ((π γ : ↥H) : MulAut V) u ∈ Y := hY _ (π γ).2 u huY
  have : w = (((π γ : ↥H) : MulAut V) u * w⁻¹)⁻¹ * ((π γ : ↥H) : MulAut V) u := by group
  rw [this]
  exact Y.mul_mem (Y.inv_mem (hZY h4)) h5

end G2

theorem eq_or_eq_of_g2NaturalDerived {L U C : Subgroup G} (hU : IsElemAbelian 2 U)
    {Z' : Subgroup (IntMod U hU)} (hZ' : ∀ v : IntMod U hU, v ∈ Z' ↔ v.val ∈ C)
    (h2 : G2NaturalDerived (autI hU L) ⊤ Z' 1) {W : Subgroup G} (hCW : C ≤ W) (hWU : W ≤ U)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : W = C ∨ W = U := by
  obtain ⟨K, _, _, hK, hR⟩ := h2
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨π, β, hRB⟩ := (H.Mathieu.realizes_iff _ (autI hU L) ⊤ Z').1 hR
  let W' : Subgroup (IntMod U hU) :=
    { carrier := {v | v.val ∈ W}
      mul_mem' := fun {a b} ha hb => by
        show (a * b).val ∈ W
        rw [IntMod.val_mul]
        exact W.mul_mem ha hb
      one_mem' := by
        show (1 : IntMod U hU).val ∈ W
        rw [IntMod.val_one]
        exact W.one_mem
      inv_mem' := fun {a} ha => by
        show (a⁻¹).val ∈ W
        rw [IntMod.val_inv]
        exact W.inv_mem ha }
  have hinv : ∀ φ ∈ autI hU L, ∀ w ∈ W', (φ : MulAut (IntMod U hU)) w ∈ W' := by
    intro φ hφ w hw
    obtain ⟨g, hg, rfl⟩ := (mem_autI hU).1 hφ
    show (convI hU g w).val ∈ W
    rw [convI_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp (hLW hg) _).mp hw
  have hZW : Z' ≤ W' := fun v hv => hCW ((hZ' v).1 hv)
  rcases eq_or_eq_of_realizesBy hRB (zornQ_g2Derived_transitive hK2) hZW le_top hinv with
    he | he
  · left
    refine le_antisymm (fun x hx => ?_) hCW
    have hxW' : IntMod.mk hU ⟨x, hWU hx⟩ ∈ W' := hx
    rw [he] at hxW'
    exact (hZ' _).1 hxW'
  · right
    refine le_antisymm hWU fun x hx => ?_
    have : IntMod.mk hU ⟨x, hx⟩ ∈ W' := he ▸ Subgroup.mem_top _
    exact this

end CFSG.Quasithin.MS93
