module

public import CFSG.Quasithin.EmptyFaithful.R3c23Def
public import CFSG.Quasithin.Background.B5FinPerm
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace R3c23

namespace Sym5

abbrev D5 : Type := ↥(G6.coreMod 5)

def pairV (a b : Fin 5) : Fin 5 → ZMod 2 :=
  fun i => (if i = a then 1 else 0) + (if i = b then 1 else 0)

theorem sum_pairV (a b : Fin 5) : ∑ i, pairV a b i = 0 := by
  revert a b
  decide +kernel

def pairM (a b : Fin 5) : D5 :=
  ⟨Multiplicative.ofAdd (pairV a b), G6.mem_coreMod.mpr (sum_pairV a b)⟩

theorem card_D5 : Nat.card D5 = 16 := by
  rw [Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd (fun x => G6.mem_coreMod) :
      D5 ≃ {f : Fin 5 → ZMod 2 // ∑ i, f i = 0}), Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem pairM_ne_one : pairM 0 1 ≠ 1 := by
  intro h
  have h' := congrFun (congrArg (fun y : D5 => Multiplicative.toAdd (y : G6.PermMod 5)) h) 0
  revert h'
  decide +kernel

theorem fc_faithful : ∀ σ : Equiv.Perm (Fin 5),
    (∀ f : Fin 5 → ZMod 2, ∑ i, f i = 0 → ∀ i, f (σ⁻¹ i) = f i) → σ = 1 := by
  decide +kernel

theorem fc_cycle : ∀ σ : Equiv.Perm (Fin 5), σ ^ 5 = 1 → σ ≠ 1 →
    ∀ f : Fin 5 → ZMod 2, ∑ i, f i = 0 → (∀ i, f (σ⁻¹ i) = f i) → f = 0 := by
  decide +kernel

theorem fc_pair : ∀ a b : Fin 5, ∃ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 ∧
    ∃ v : Fin 5 → ZMod 2, ∑ i, v i = 0 ∧ ∀ i, v (σ⁻¹ i) + -v i = pairV a b i := by
  decide +kernel

theorem fc_gen : ∀ f : Fin 5 → ZMod 2, ∑ i, f i = 0 →
    ∃ a b c d : Fin 5, ∀ i, f i = pairV a b i + pairV c d i := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem fc_no_three : ∀ x₁ : Equiv.Perm (Fin 5), x₁ * x₁ = 1 → x₁ ≠ 1 →
    ∀ x₂ : Equiv.Perm (Fin 5), x₂ * x₂ = 1 → x₁ * x₂ = x₂ * x₁ → x₂ ≠ 1 → x₂ ≠ x₁ →
    ∀ x₃ : Equiv.Perm (Fin 5), x₃ * x₃ = 1 → x₁ * x₃ = x₃ * x₁ → x₂ * x₃ = x₃ * x₂ →
      x₃ ≠ 1 → x₃ ≠ x₁ → x₃ ≠ x₂ → x₃ ≠ x₁ * x₂ → False := by
  decide +kernel

def fixVec (a b : Equiv.Perm (Fin 5)) : Finset (Fin 5 → ZMod 2) :=
  Finset.univ.filter fun f => ∑ i, f i = 0 ∧ (∀ i, f (a⁻¹ i) = f i) ∧ ∀ i, f (b⁻¹ i) = f i

theorem fc_count : ∀ a b : Equiv.Perm (Fin 5), a * a = 1 → b * b = 1 → a * b = b * a →
    ({1, a, b, a * b} : Finset (Equiv.Perm (Fin 5))).card * (fixVec a b).card ≤ 16 := by
  decide +kernel

def fixSet (B' : Subgroup (Equiv.Perm (Fin 5))) : Set D5 :=
  {x | ∀ σ ∈ B', G6.coreAct 5 σ x = x}

theorem exists_two_gen (B' : Subgroup (Equiv.Perm (Fin 5)))
    (hc : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a) (hs : ∀ a ∈ B', a * a = 1) :
    ∃ a ∈ B', ∃ b ∈ B', ∀ σ ∈ B', σ = 1 ∨ σ = a ∨ σ = b ∨ σ = a * b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁, h1⟩ := hcon 1 B'.one_mem 1 B'.one_mem
  obtain ⟨x₂, hx₂, h2⟩ := hcon x₁ hx₁ 1 B'.one_mem
  obtain ⟨x₃, hx₃, h3⟩ := hcon x₁ hx₁ x₂ hx₂
  exact fc_no_three x₁ (hs x₁ hx₁) h1.1 x₂ (hs x₂ hx₂) (hc x₁ hx₁ x₂ hx₂) h2.1 h2.2.1
    x₃ (hs x₃ hx₃) (hc x₁ hx₁ x₃ hx₃) (hc x₂ hx₂ x₃ hx₃) h3.1 h3.2.1 h3.2.2.1 h3.2.2.2

theorem card_le_card_finset {α β : Type*} (s : Set α) (f : α → β) (hf : Function.Injective f)
    (t : Finset β) (h : ∀ x ∈ s, f x ∈ t) : Nat.card ↥s ≤ t.card := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_le_card_of_injective (fun x : ↥s => (⟨f x.1, h x.1 x.2⟩ : ↥t)) ?_
  intro x y hxy
  have h' : f x.1 = f y.1 := congrArg (Subtype.val : ↥t → β) hxy
  exact Subtype.ext (hf h')

theorem count_fix (B' : Subgroup (Equiv.Perm (Fin 5)))
    (hc : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a) (hs : ∀ a ∈ B', a * a = 1) :
    Nat.card ↥B' * Nat.card ↥(fixSet B') ≤ 16 := by
  obtain ⟨a, ha, b, hb, hgen⟩ := exists_two_gen B' hc hs
  have h1 : Nat.card ↥B' ≤ ({1, a, b, a * b} : Finset (Equiv.Perm (Fin 5))).card :=
    card_le_card_finset (B' : Set (Equiv.Perm (Fin 5))) id Function.injective_id _ fun σ hσ => by
      simpa only [Finset.mem_insert, Finset.mem_singleton, id] using hgen σ hσ
  have h2 : Nat.card ↥(fixSet B') ≤ (fixVec a b).card := by
    refine card_le_card_finset (fixSet B') (fun x : D5 => Multiplicative.toAdd (x : G6.PermMod 5))
      (fun x y h => Subtype.ext (Multiplicative.toAdd.injective h)) _ fun x hx => ?_
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, G6.mem_coreMod.mp x.2, ?_, ?_⟩
    · exact fun i => congrFun (congrArg (fun y : D5 => Multiplicative.toAdd (y : G6.PermMod 5))
        (hx a ha)) i
    · exact fun i => congrFun (congrArg (fun y : D5 => Multiplicative.toAdd (y : G6.PermMod 5))
        (hx b hb)) i
  exact (Nat.mul_le_mul h1 h2).trans (fc_count a b (hs a ha) (hs b hb) (hc a ha b hb))

theorem card_le_ker_mul {A M : Type*} [Group A] [Group M] (f : A →* M) (K : Subgroup A)
    (S : Set M) (hK : ∀ k ∈ K, f k ∈ S) [Finite ↥f.ker] [Finite ↥S] :
    Nat.card ↥K ≤ Nat.card ↥f.ker * Nat.card ↥S := by
  rw [← Subgroup.card_ker_mul_card_range (f.comp K.subtype)]
  refine Nat.mul_le_mul ?_ ?_
  · refine Nat.card_le_card_of_injective
      (fun k : ↥(f.comp K.subtype).ker =>
        (⟨((k.1 : ↥K) : A), MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp k.2)⟩ : ↥f.ker)) ?_
    intro k₁ k₂ h
    have h' : ((k₁.1 : ↥K) : A) = ((k₂.1 : ↥K) : A) := congrArg (Subtype.val : ↥f.ker → A) h
    exact Subtype.ext (Subtype.ext h')
  · have hS : ∀ y : ↥(f.comp K.subtype).range, (y : M) ∈ S := by
      intro y
      obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp y.2
      rw [← hk]
      exact hK k.1 k.2
    refine Nat.card_le_card_of_injective
      (fun y : ↥(f.comp K.subtype).range => (⟨(y : M), hS y⟩ : ↥S)) ?_
    intro y₁ y₂ h
    have h' : (y₁ : M) = (y₂ : M) := congrArg (Subtype.val : ↥S → M) h
    exact Subtype.ext h'

theorem allOnes_not_mem_coreMod : G6.allOnes 5 ∉ G6.coreMod 5 := by
  rw [G6.mem_coreMod]
  decide +kernel

theorem ker_symDn : (FFModel.symDn 5).ker = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
  rcases B5FinPerm.mem_zpowers_allOnes_iff.mp h1 with h | h
  · exact h
  · rw [h] at h2
    exact absurd h2 allOnes_not_mem_coreMod

variable {V : Type} [CommGroup V]

structure RealizationData (G : Subgroup (MulAut V)) (W C : Subgroup V) where
  π : Equiv.Perm (Fin 5) →* ↥G
  β : ↥W →* D5
  surj_π : Function.Surjective π
  surj_β : Function.Surjective β
  CW : C ≤ W
  Winv : ∀ (g : ↥G) (u : V), u ∈ W → (g : MulAut V) u ∈ W
  ker_β : ∀ u : ↥W, β u = 1 ↔ (u : V) ∈ C
  equiv : ∀ (σ : Equiv.Perm (Fin 5)) (u : ↥W),
    β ⟨((π σ : ↥G) : MulAut V) (u : V), Winv _ _ u.2⟩ = G6.coreAct 5 σ (β u)

variable {G : Subgroup (MulAut V)} {W C : Subgroup V}

theorem exists_data (h : SymmetricNatural G W C 5) : Nonempty (RealizationData G W C) := by
  obtain ⟨π, hπs, hCW, -, hWinv, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  have hK : (FFModel.symDn 5).ker.subgroupOf (FFModel.symDn 5).sec = ⊥ := by
    rw [ker_symDn]
    exact Subgroup.bot_subgroupOf _
  let ε : ↥(FFModel.symDn 5).sec ⧸ (FFModel.symDn 5).ker.subgroupOf (FFModel.symDn 5).sec →*
      ↥(FFModel.symDn 5).sec := QuotientGroup.lift _ (MonoidHom.id _) (by rw [hK]; exact bot_le)
  have hε : ∀ m : ↥(FFModel.symDn 5).sec, ε (QuotientGroup.mk m) = m := fun m => rfl
  refine ⟨{
    π := π
    β := ε.comp β
    surj_π := hπs
    surj_β := ?_
    CW := hCW
    Winv := hWinv
    ker_β := ?_
    equiv := ?_ }⟩
  · intro m
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
    exact ⟨u, (congrArg ε hu).trans (hε m)⟩
  · intro u
    rw [← hβk u]
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hεu : ε (β u) = m := (congrArg ε hm.symm).trans (hε m)
    constructor
    · intro h1
      have h2 : m = 1 := hεu.symm.trans h1
      rw [← hm, h2]
      exact QuotientGroup.mk_one _
    · intro h1
      show ε (β u) = 1
      rw [h1, map_one]
  · intro σ u
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hm' : (FFModel.symDn 5).act σ (m : (FFModel.symDn 5).Amb) ∈ (FFModel.symDn 5).sec :=
      hsec σ m m.2
    have key := hβe σ u m (hWinv _ _ u.2) hm' hm.symm
    have hεu : (ε.comp β) u = m := (congrArg ε hm.symm).trans (hε m)
    refine (congrArg ε key).trans ?_
    refine Eq.trans (b := G6.coreAct 5 σ m) rfl ?_
    exact congrArg (⇑(G6.coreAct 5 σ)) hεu.symm

namespace RealizationData

theorem injective_π (d : RealizationData G W C) : Function.Injective d.π := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hfix : ∀ x : D5, G6.coreAct 5 σ x = x := by
    intro x
    obtain ⟨u, rfl⟩ := d.surj_β x
    have h2 : (⟨((d.π σ : ↥G) : MulAut V) (u : V), d.Winv _ _ u.2⟩ : ↥W) = u := by
      apply Subtype.ext
      simp [hσ]
    have h1 := d.equiv σ u
    rw [h2] at h1
    exact h1.symm
  refine fc_faithful σ fun f hf i => ?_
  exact congrFun (congrArg (fun y : D5 => Multiplicative.toAdd (y : G6.PermMod 5))
    (hfix ⟨Multiplicative.ofAdd f, G6.mem_coreMod.mpr hf⟩)) i

end RealizationData

def preimg (π : Equiv.Perm (Fin 5) →* ↥G) (B : Subgroup (MulAut V)) :
    Subgroup (Equiv.Perm (Fin 5)) :=
  (B.subgroupOf G).comap π

theorem mem_preimg {π : Equiv.Perm (Fin 5) →* ↥G} {B : Subgroup (MulAut V)}
    {σ : Equiv.Perm (Fin 5)} : σ ∈ preimg π B ↔ ((π σ : ↥G) : MulAut V) ∈ B := Iff.rfl

namespace RealizationData

theorem card_preimg (d : RealizationData G W C) {B : Subgroup (MulAut V)} (hBG : B ≤ G) :
    Nat.card ↥(preimg d.π B) = Nat.card ↥B := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun σ : ↥(preimg d.π B) => (⟨((d.π σ.1 : ↥G) : MulAut V), mem_preimg.mp σ.2⟩ : ↥B))
    ⟨?_, ?_⟩)
  · intro σ τ h
    have h' : d.π σ.1 = d.π τ.1 :=
      Subtype.ext (congrArg (Subtype.val : ↥B → MulAut V) h)
    exact Subtype.ext (d.injective_π h')
  · intro b
    obtain ⟨σ, hσ⟩ := d.surj_π ⟨(b : MulAut V), hBG b.2⟩
    refine ⟨⟨σ, mem_preimg.mpr (by rw [hσ]; exact b.2)⟩, Subtype.ext ?_⟩
    exact congrArg (Subtype.val : ↥G → MulAut V) hσ

theorem act_eq (d : RealizationData G W C) {σ : Equiv.Perm (Fin 5)} {w : V} (hw : w ∈ W)
    (h : ((d.π σ : ↥G) : MulAut V) w * w⁻¹ ∈ C) :
    G6.coreAct 5 σ (d.β ⟨w, hw⟩) = d.β ⟨w, hw⟩ := by
  have h1 := d.equiv σ ⟨w, hw⟩
  have h2 : d.β (⟨((d.π σ : ↥G) : MulAut V) w, d.Winv _ _ hw⟩ * (⟨w, hw⟩ : ↥W)⁻¹) = 1 :=
    (d.ker_β _).2 h
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [← h1]
  exact h2

theorem card_ker (d : RealizationData G W C) : Nat.card ↥d.β.ker = Nat.card ↥C :=
  Nat.card_congr
    { toFun := fun u => ⟨(u.1 : V), (d.ker_β u.1).1 (MonoidHom.mem_ker.mp u.2)⟩
      invFun := fun c => ⟨⟨(c : V), d.CW c.2⟩, MonoidHom.mem_ker.mpr ((d.ker_β _).2 c.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_W (d : RealizationData G W C) : Nat.card ↥W = 16 * Nat.card ↥C := by
  rw [← Subgroup.card_ker_mul_card_of_surjective d.surj_β, d.card_ker, card_D5, mul_comm]

theorem natCount (d : RealizationData G W C) [Finite V] : NatCount G W C := by
  intro B hBG hB
  have hcardB : Nat.card ↥B = Nat.card ↥(preimg d.π B) := (d.card_preimg hBG).symm
  have hc : ∀ a ∈ preimg d.π B, ∀ b ∈ preimg d.π B, a * b = b * a := by
    intro a ha b hb
    apply d.injective_π
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact hB.1 _ (mem_preimg.mp ha) _ (mem_preimg.mp hb)
  have hs : ∀ a ∈ preimg d.π B, a * a = 1 := by
    intro a ha
    apply d.injective_π
    apply Subtype.ext
    rw [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one, ← sq]
    exact hB.2 _ (mem_preimg.mp ha)
  have hle : fixMod B W C ≤ W := fun w hw => hw.1
  have hKcard : Nat.card ↥((fixMod B W C).subgroupOf W) = Nat.card ↥(fixMod B W C) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hfib : Nat.card ↥((fixMod B W C).subgroupOf W) ≤
      Nat.card ↥C * Nat.card ↥(fixSet (preimg d.π B)) := by
    have := card_le_ker_mul d.β ((fixMod B W C).subgroupOf W) (fixSet (preimg d.π B)) ?_
    · rwa [d.card_ker] at this
    · intro k hk σ hσ
      exact d.act_eq k.2 ((mem_fixMod.mp (Subgroup.mem_subgroupOf.mp hk)).2 _ (mem_preimg.mp hσ))
  have hcount := count_fix (preimg d.π B) hc hs
  calc Nat.card ↥B * Nat.card ↥(fixMod B W C)
      = Nat.card ↥(preimg d.π B) * Nat.card ↥((fixMod B W C).subgroupOf W) := by
        rw [hcardB, hKcard]
    _ ≤ Nat.card ↥(preimg d.π B) * (Nat.card ↥C * Nat.card ↥(fixSet (preimg d.π B))) :=
        Nat.mul_le_mul_left _ hfib
    _ = Nat.card ↥C * (Nat.card ↥(preimg d.π B) * Nat.card ↥(fixSet (preimg d.π B))) := by ring
    _ ≤ Nat.card ↥C * 16 := Nat.mul_le_mul_left _ hcount
    _ = Nat.card ↥W := by rw [d.card_W, mul_comm]

theorem exists_not_mem (d : RealizationData G W C) : ∃ w ∈ W, w ∉ C := by
  obtain ⟨u, hu⟩ := d.surj_β (pairM 0 1)
  refine ⟨(u : V), u.2, fun huC => pairM_ne_one ?_⟩
  rw [← hu]
  exact (d.ker_β u).2 huC

theorem mem_of_fixed (d : RealizationData G W C) {L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hL : Nat.card ↥L = 60) {w : V} (hw : w ∈ W) (h : ∀ l ∈ L, l w * w⁻¹ ∈ C) : w ∈ C := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 5 (by rw [hL]; norm_num)
  let ι : ↥L →* ↥G := Subgroup.inclusion hLG
  let ρ : Equiv.Perm (Fin 5) ≃* ↥G := MulEquiv.ofBijective d.π ⟨d.injective_π, d.surj_π⟩
  have hord : orderOf (ρ.symm (ι g)) = 5 := by
    rw [MulEquiv.orderOf_eq ρ.symm (ι g), orderOf_injective ι (Subgroup.inclusion_injective hLG) g]
    exact hg
  have hσ5 : ρ.symm (ι g) ^ 5 = 1 := by
    have h5 := pow_orderOf_eq_one (ρ.symm (ι g))
    rwa [hord] at h5
  have hσ1 : ρ.symm (ι g) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    norm_num at hord
  have hπσ : d.π (ρ.symm (ι g)) = ι g := ρ.apply_symm_apply (ι g)
  have hl : ((d.π (ρ.symm (ι g)) : ↥G) : MulAut V) w * w⁻¹ ∈ C := by
    rw [hπσ]
    exact h _ g.2
  have hfix := d.act_eq hw hl
  have h0 := fc_cycle _ hσ5 hσ1 (Multiplicative.toAdd ((d.β ⟨w, hw⟩ : D5) : G6.PermMod 5))
    (G6.mem_coreMod.mp (d.β ⟨w, hw⟩).2)
    (fun i => congrFun (congrArg (fun y : D5 => Multiplicative.toAdd (y : G6.PermMod 5)) hfix) i)
  have h1 : d.β ⟨w, hw⟩ = 1 :=
    Subtype.ext (Multiplicative.toAdd.injective (h0.trans rfl))
  exact (d.ker_β ⟨w, hw⟩).1 h1

theorem le_commMod_sup (d : RealizationData G W C) {L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hL : Nat.card ↥L = 60) : W ≤ commMod L W ⊔ C := by
  have hcard : Nat.card ↥(preimg d.π L) = 60 := (d.card_preimg hLG).trans hL
  have hidx : (preimg d.π L).index = 2 := by
    have h := Subgroup.card_mul_index (preimg d.π L)
    rw [hcard, Nat.card_perm] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have h5 : (5 : ℕ).factorial = 120 := rfl
    omega
  have hodd : ∀ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 → σ ∈ preimg d.π L := by
    intro σ h3
    have h4 : σ = (σ ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
    have hm := Subgroup.sq_mem_of_index_two hidx (σ ^ 2)
    rwa [← h4] at hm
  let Q : Subgroup D5 :=
    Subgroup.closure {y | ∃ σ ∈ preimg d.π L, ∃ v : D5, y = G6.coreAct 5 σ v * v⁻¹}
  have hpair : ∀ a b : Fin 5, pairM a b ∈ Q := by
    intro a b
    obtain ⟨σ, hσ3, v, hv0, hv⟩ := fc_pair a b
    have hmem : G6.coreAct 5 σ (⟨Multiplicative.ofAdd v, G6.mem_coreMod.mpr hv0⟩ : D5) *
        (⟨Multiplicative.ofAdd v, G6.mem_coreMod.mpr hv0⟩ : D5)⁻¹ ∈ Q :=
      Subgroup.subset_closure ⟨σ, hodd σ hσ3, _, rfl⟩
    convert hmem using 1
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    exact (hv i).symm
  have hQtop : ∀ x : D5, x ∈ Q := by
    intro x
    obtain ⟨a, b, c, e, h⟩ :=
      fc_gen (Multiplicative.toAdd (x : G6.PermMod 5)) (G6.mem_coreMod.mp x.2)
    have hx : x = pairM a b * pairM c e := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      funext i
      exact h i
    rw [hx]
    exact Q.mul_mem (hpair a b) (hpair c e)
  let T : Subgroup D5 := ((commMod L W).subgroupOf W).map d.β
  have hQT : Q ≤ T := by
    refine (Subgroup.closure_le T).mpr ?_
    rintro y ⟨σ, hσ, v, rfl⟩
    obtain ⟨u, rfl⟩ := d.surj_β v
    refine ⟨⟨((d.π σ : ↥G) : MulAut V) (u : V), d.Winv _ _ u.2⟩ * u⁻¹, ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨((d.π σ : ↥G) : MulAut V), mem_preimg.mp hσ, u, u.2, rfl⟩
    · rw [map_mul, map_inv, d.equiv σ u]
  intro w hw
  obtain ⟨t, ht, hβt⟩ := hQT (hQtop (d.β ⟨w, hw⟩))
  have hmem : w * (t : V)⁻¹ ∈ C := by
    refine (d.ker_β (⟨w, hw⟩ * t⁻¹)).1 ?_
    rw [map_mul, map_inv, hβt, mul_inv_cancel]
  have hw' : w = (w * (t : V)⁻¹) * (t : V) := (inv_mul_cancel_right w t).symm
  rw [hw']
  exact mul_mem (Subgroup.mem_sup_right hmem) (Subgroup.mem_sup_left ht)

end RealizationData

end Sym5

theorem sym5PieceFacts : Sym5PieceFacts := by
  intro V _ _ G L W C hnat hLG hL60
  obtain ⟨d⟩ := Sym5.exists_data hnat
  exact ⟨d.natCount, d.CW, d.exists_not_mem, fun w hw h => d.mem_of_fixed hLG hL60 hw h,
    d.le_commMod_sup hLG hL60⟩

end R3c23

end CFSG.Quasithin
