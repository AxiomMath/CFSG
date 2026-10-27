module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Descent
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType.U63TB

open CFSG.StandardType CFSG.StandardType.Line63

section Pres

variable {L' : Type} [Group L'] [Finite L']

@[expose] def presZ (Z : Subgroup L') : Subgroup (MulAut L') where
  carrier := {φ | ∀ z ∈ Z, φ z ∈ Z}
  one_mem' := fun z hz => hz
  mul_mem' := fun {a b} ha hb z hz => ha (b z) (hb z hz)
  inv_mem' := by
    intro φ hφ z hz
    have hinj : Function.Injective (fun w : Z => (⟨φ w, hφ w w.2⟩ : Z)) := by
      intro a b h
      exact Subtype.ext (φ.injective (congrArg Subtype.val h))
    obtain ⟨w, hw⟩ := Finite.injective_iff_surjective.mp hinj ⟨z, hz⟩
    have hwz : φ w = z := congrArg Subtype.val hw
    rw [← hwz]
    simpa using w.2

variable (Z : Subgroup L') [Z.Normal]

theorem map_eq_of_mem_presZ {φ : MulAut L'} (hφ : φ ∈ presZ Z) :
    Z.map φ.toMonoidHom = Z := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hφ z hz
  · intro z hz
    exact ⟨φ⁻¹ z, (presZ Z).inv_mem hφ z hz, by simp⟩

@[expose] noncomputable def redAut (φ : presZ Z) : MulAut (L' ⧸ Z) :=
  QuotientGroup.congr Z Z φ.1 (map_eq_of_mem_presZ Z φ.2)

theorem redAut_mk (φ : presZ Z) (l : L') :
    redAut Z φ (l : L' ⧸ Z) = ((φ.1 l : L') : L' ⧸ Z) :=
  QuotientGroup.congr_mk _ _ _ _ l

@[expose] noncomputable def redHom : presZ Z →* MulAut (L' ⧸ Z) where
  toFun := redAut Z
  map_one' := by
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rw [redAut_mk]
    rfl
  map_mul' := fun a b => by
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [MulAut.mul_apply, redAut_mk]
    rfl

theorem redHom_mk (φ : presZ Z) (l : L') :
    redHom Z φ (l : L' ⧸ Z) = ((φ.1 l : L') : L' ⧸ Z) :=
  redAut_mk Z φ l

@[expose] def conjP (n : L') : presZ Z := ⟨MulAut.conj n, fun z hz => by
  simpa [MulAut.conj_apply] using (inferInstance : Z.Normal).conj_mem z hz n⟩

theorem conjP_coe (n : L') : (conjP Z n).1 = MulAut.conj n := rfl

theorem redHom_conjP (n : L') : redHom Z (conjP Z n) = MulAut.conj (n : L' ⧸ Z) := by
  ext x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  rw [redHom_mk]
  simp [conjP_coe, MulAut.conj_apply]

end Pres

theorem aut_eq_one_of_central {L' : Type} [Group L'] {Z : Subgroup L'}
    (hZ : Z ≤ Subgroup.center L') (hperf : commutator L' = ⊤) {φ : MulAut L'}
    (h : ∀ l : L', l⁻¹ * φ l ∈ Z) : φ = 1 := by
  have hcen : ∀ y ∈ Z, ∀ g : L', g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hZ hy) g
  letI : CommGroup Z :=
    { (inferInstance : Group Z) with mul_comm := fun x y => Subtype.ext (hcen y y.2 x) }
  let f : L' →* Z :=
    { toFun := fun l => ⟨l⁻¹ * φ l, h l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun l m => Subtype.ext (by
        show (l * m)⁻¹ * φ (l * m) = l⁻¹ * φ l * (m⁻¹ * φ m)
        have hc := hcen _ (h l) m⁻¹
        calc (l * m)⁻¹ * φ (l * m) = m⁻¹ * (l⁻¹ * φ l) * φ m := by rw [map_mul]; group
          _ = (l⁻¹ * φ l) * m⁻¹ * φ m := by rw [hc]
          _ = l⁻¹ * φ l * (m⁻¹ * φ m) := by group) }
  have hf : ∀ l, f l = 1 := fun l =>
    Abelianization.commutator_subset_ker f (by rw [hperf]; exact Subgroup.mem_top l)
  ext l
  have h1 : l⁻¹ * φ l = 1 := congrArg Subtype.val (hf l)
  exact (inv_mul_eq_one.mp h1).symm

section Inj

variable {L' : Type} [Group L'] [Finite L'] (Z : Subgroup L') [Z.Normal]

theorem redHom_injective (hZ : Z ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    Function.Injective (redHom Z) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  have h : ∀ l : L', l⁻¹ * φ.1 l ∈ Z := by
    intro l
    have := congrArg (fun f : MulAut (L' ⧸ Z) => f (l : L' ⧸ Z)) hφ
    simp only [redHom_mk, MulAut.one_apply, map_one] at this
    exact QuotientGroup.eq.mp this.symm
  exact Subtype.ext (aut_eq_one_of_central hZ hperf h)

end Inj

section Two

variable {L' : Type} [Group L'] [Finite L']

@[expose] def twoSub (N : Subgroup L') (hN : N ≤ Subgroup.center L') : Subgroup L' where
  carrier := {z | z ∈ N ∧ z ^ (2 ^ Nat.card L') = 1}
  one_mem' := ⟨N.one_mem, one_pow _⟩
  mul_mem' := fun {x y} hx hy => ⟨N.mul_mem hx.1 hy.1, by
    rw [Commute.mul_pow (Subgroup.mem_center_iff.mp (hN hy.1) x), hx.2, hy.2, one_mul]⟩
  inv_mem' := fun {x} hx => ⟨N.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

variable {N : Subgroup L'} (hN : N ≤ Subgroup.center L')

theorem mem_twoSub {z : L'} : z ∈ twoSub N hN ↔ z ∈ N ∧ z ^ (2 ^ Nat.card L') = 1 := Iff.rfl

theorem twoSub_le_center : twoSub N hN ≤ Subgroup.center L' := fun _ hz => hN hz.1

theorem isPGroup_twoSub : IsPGroup 2 (twoSub N hN) :=
  fun g => ⟨Nat.card L', Subtype.ext (by simpa using g.2.2)⟩

instance twoSub_normal : (twoSub N hN).Normal :=
  ⟨fun y hy g => by
    rw [(Subgroup.mem_center_iff.mp (twoSub_le_center hN hy) g), mul_inv_cancel_right]
    exact hy⟩

end Two

section Quot

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
  (hker : ψ.ker ≤ Subgroup.center L')

@[expose] noncomputable def psi1 : L' ⧸ twoSub ψ.ker hker →* R :=
  QuotientGroup.lift _ ψ (fun _ hz => hz.1)

theorem psi1_mk (l : L') : psi1 hker (l : L' ⧸ twoSub ψ.ker hker) = ψ l :=
  QuotientGroup.lift_mk _ _ _

theorem psi1_surjective (hψ : Function.Surjective ψ) : Function.Surjective (psi1 hker) :=
  fun r => by
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨l, psi1_mk hker l⟩

theorem mem_ker_psi1 {l : L'} : (l : L' ⧸ twoSub ψ.ker hker) ∈ (psi1 hker).ker ↔ l ∈ ψ.ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, psi1_mk]

theorem psi1_ker_central : (psi1 hker).ker ≤ Subgroup.center (L' ⧸ twoSub ψ.ker hker) := by
  intro x hx
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  have hl : l ∈ ψ.ker := (mem_ker_psi1 hker).mp hx
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hker hl) g]

theorem commutator_quot (hperf : commutator L' = ⊤) :
    commutator (L' ⧸ twoSub ψ.ker hker) = ⊤ := by
  have hπs : Function.Surjective (QuotientGroup.mk' (twoSub ψ.ker hker)) :=
    QuotientGroup.mk'_surjective _
  have : (commutator L').map (QuotientGroup.mk' (twoSub ψ.ker hker)) =
      commutator (L' ⧸ twoSub ψ.ker hker) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hπs]
  rw [← this, hperf, Subgroup.map_top_of_surjective _ hπs]

theorem odd_card_ker_psi1 : Odd (Nat.card (psi1 hker).ker) := by
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hne)
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective x.1
  have hx2 : x.1 ^ 2 = 1 := by
    have := congrArg Subtype.val (pow_orderOf_eq_one x)
    rw [hx] at this
    simpa using this
  have hl2 : l ^ 2 ∈ twoSub ψ.ker hker := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hl, hx2]
  have hlker : l ∈ ψ.ker := by
    rw [← mem_ker_psi1 hker, hl]
    exact x.2
  have hlZ : l ∈ twoSub ψ.ker hker := ⟨hlker, pow_two_pow_card l (j := Nat.card L' + 1)
    (by rw [pow_succ, pow_mul', hl2.2])⟩
  have : x = 1 := Subtype.ext (by rw [← hl]; exact (QuotientGroup.eq_one_iff l).mpr hlZ)
  rw [this, orderOf_one] at hx
  norm_num at hx

theorem mem_presZ_of_ker {f : MulAut L'} (hf : ∀ z ∈ ψ.ker, f z ∈ ψ.ker) :
    f ∈ presZ (twoSub ψ.ker hker) := fun z hz =>
  ⟨hf z hz.1, by rw [← map_pow, hz.2, map_one]⟩

theorem preserves_ker {I : Set (MulAut R)} {a : MulAut L'}
    (h : ∃ x ∈ I, ∀ l : L', x (ψ l) = ψ (a l)) {z : L'} (hz : z ∈ ψ.ker) : a z ∈ ψ.ker := by
  obtain ⟨x, -, hx⟩ := h
  rw [MonoidHom.mem_ker, ← hx, MonoidHom.mem_ker.mp hz, map_one]

end Quot

section Sub

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
  (hker : ψ.ker ≤ Subgroup.center L')

@[expose] noncomputable def redSub {S : Subgroup (MulAut L')}
    (hS : S ≤ presZ (twoSub ψ.ker hker)) : S →* MulAut (L' ⧸ twoSub ψ.ker hker) :=
  (redHom (twoSub ψ.ker hker)).comp (Subgroup.inclusion hS)

variable {S : Subgroup (MulAut L')} (hS : S ≤ presZ (twoSub ψ.ker hker))

theorem redSub_mk (s : S) (l : L') :
    redSub hker hS s (l : L' ⧸ twoSub ψ.ker hker) = ((s.1 l : L') : L' ⧸ twoSub ψ.ker hker) :=
  redHom_mk _ _ l

theorem redSub_injective (hperf : commutator L' = ⊤) : Function.Injective (redSub hker hS) :=
  (redHom_injective _ (twoSub_le_center hker) hperf).comp (Subgroup.inclusion_injective hS)

theorem isElemAbelian_range_redSub {p : ℕ} (hA : CFSG.Open.IsElemAbelian p S) :
    CFSG.Open.IsElemAbelian p (redSub hker hS).range := by
  have hAc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show redSub hker hS a * redSub hker hS b = redSub hker hS b * redSub hker hS a
    have : a * b = b * a := Subtype.ext (hAc a.1 a.2 b.1 b.2)
    rw [← map_mul, this, map_mul]
  · rintro _ ⟨a, rfl⟩
    have : a ^ p = 1 := Subtype.ext (by simpa using hA.2 a.1 a.2)
    rw [← map_pow, this, map_one]

theorem card_range_redSub (hperf : commutator L' = ⊤) :
    Nat.card (redSub hker hS).range = Nat.card S :=
  (Nat.card_congr (MonoidHom.ofInjective (redSub_injective hker hS hperf)).toEquiv).symm

theorem redSub_hAI {I : Set (MulAut R)}
    (hSI : ∀ a ∈ S, ∃ x ∈ I, ∀ l : L', x (ψ l) = ψ (a l)) :
    ∀ a₁ ∈ (redSub hker hS).range, ∃ x ∈ I, ∀ l₁ : L' ⧸ twoSub ψ.ker hker,
      x (psi1 hker l₁) = psi1 hker (a₁ l₁) := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨x, hx, hxa⟩ := hSI a.1 a.2
  refine ⟨x, hx, fun l₁ => ?_⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l₁
  rw [psi1_mk, redSub_mk, psi1_mk]
  exact hxa l

theorem redSub_conj (n : L') (hc : MulAut.conj n ∈ S) :
    redSub hker hS ⟨MulAut.conj n, hc⟩ = MulAut.conj (n : L' ⧸ twoSub ψ.ker hker) :=
  redHom_conjP (twoSub ψ.ker hker) n

end Sub

section Lift

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
  (hker : ψ.ker ≤ Subgroup.center L')

theorem selfCent_quot {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAle : A ≤ presZ (twoSub ψ.ker hker)) (hsc : GGTorusSelfCent 3 A) :
    GGTorusSelfCent 3 (redSub hker hAle).range := by
  classical
  have hZc := twoSub_le_center hker
  have hZ2 := isPGroup_twoSub hker
  have hAp : ∀ a ∈ A, a ^ 3 = 1 := hA.2
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAp g.1 g.2)⟩
  have hT3 : IsPGroup 3 (⊥ : Subgroup L') :=
    fun g => ⟨0, Subtype.ext (by simp [Subgroup.mem_bot.mp g.2])⟩
  intro m hfix hm3
  obtain ⟨n₀, rfl⟩ := QuotientGroup.mk_surjective m
  have hn₀ : ∀ a ∈ A, n₀ * (a n₀)⁻¹ ∈ (⊥ : Subgroup L') ⊔ twoSub ψ.ker hker := by
    intro a ha
    have h1 := hfix (redSub hker hAle ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
    rw [redSub_mk] at h1
    have h2 : (a n₀)⁻¹ * n₀ ∈ twoSub ψ.ker hker := QuotientGroup.eq.mp h1
    have h3 : n₀ * (a n₀)⁻¹ = (a n₀) * ((a n₀)⁻¹ * n₀) * (a n₀)⁻¹ := by group
    rw [h3]
    exact Subgroup.mem_sup_right
      ((inferInstance : (twoSub ψ.ker hker).Normal).conj_mem _ h2 (a n₀))
  obtain ⟨z, hz, hzfix⟩ := exists_lift_weyl hZc hZ2 hT3 hA3 (fun a ha z hz => hAle ha z hz)
    (fun a _ t ht => by rw [Subgroup.mem_bot.mp ht, map_one]) n₀ hn₀
  have hfixu : ∀ a ∈ A, a (n₀ * z) = n₀ * z := by
    intro a ha
    have := Subgroup.mem_bot.mp (hzfix a ha)
    exact (mul_inv_eq_one.mp this).symm
  have hzmk : ((z : L') : L' ⧸ twoSub ψ.ker hker) = 1 := (QuotientGroup.eq_one_iff z).mpr hz
  have humk : ((n₀ * z : L') : L' ⧸ twoSub ψ.ker hker) = (n₀ : L' ⧸ twoSub ψ.ker hker) := by
    rw [QuotientGroup.mk_mul, hzmk, mul_one]
  have hu3 : (n₀ * z) ^ 3 ∈ twoSub ψ.ker hker := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, humk]
    exact hm3
  obtain ⟨j, hj⟩ : ∃ j, 4 ^ Nat.card L' = 3 * j + 1 :=
    ⟨4 ^ Nat.card L' / 3, by
      have : 4 ^ Nat.card L' % 3 = 1 := by rw [Nat.pow_mod]; norm_num
      omega⟩
  have hM2 : 4 ^ Nat.card L' = 2 ^ Nat.card L' * 2 ^ Nat.card L' := by
    rw [← mul_pow]
    norm_num
  have hvfix : ∀ a ∈ A, a ((n₀ * z) ^ 4 ^ Nat.card L') = (n₀ * z) ^ 4 ^ Nat.card L' :=
    fun a ha => by rw [map_pow, hfixu a ha]
  have hv3 : ((n₀ * z) ^ 4 ^ Nat.card L') ^ 3 = 1 := by
    rw [← pow_mul, pow_mul', hM2, pow_mul, hu3.2, one_pow]
  have hvmk : (((n₀ * z) ^ 4 ^ Nat.card L' : L') : L' ⧸ twoSub ψ.ker hker) =
      (n₀ : L' ⧸ twoSub ψ.ker hker) := by
    rw [QuotientGroup.mk_pow, humk, hj, pow_succ, pow_mul, hm3, one_pow, one_mul]
  have hcA : MulAut.conj ((n₀ * z) ^ 4 ^ Nat.card L') ∈ A := hsc _ hvfix hv3
  refine ⟨⟨MulAut.conj ((n₀ * z) ^ 4 ^ Nat.card L'), hcA⟩, ?_⟩
  rw [← hvmk]
  exact redSub_conj hker hAle _ hcA

theorem exists_lift_W {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAle : A ≤ presZ (twoSub ψ.ker hker)) {w : L' ⧸ twoSub ψ.ker hker}
    (hw : ∀ a₁ ∈ (redSub hker hAle).range, (w * (a₁ w)⁻¹) ^ 3 = 1 ∧
      ∀ a₁' ∈ (redSub hker hAle).range, a₁' (w * (a₁ w)⁻¹) = w * (a₁ w)⁻¹) :
    ∃ n : L', (n : L' ⧸ twoSub ψ.ker hker) = w ∧
      ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹ := by
  classical
  have hZc := twoSub_le_center hker
  have hZ2 := isPGroup_twoSub hker
  have hAp : ∀ a ∈ A, a ^ 3 = 1 := hA.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAp g.1 g.2)⟩
  obtain ⟨n₀, rfl⟩ := QuotientGroup.mk_surjective w
  have hu : ∀ a : A, ((n₀ * (a.1 n₀)⁻¹ : L') : L' ⧸ twoSub ψ.ker hker) =
      (n₀ : L' ⧸ twoSub ψ.ker hker) * (redSub hker hAle a (n₀ : L' ⧸ twoSub ψ.ker hker))⁻¹ :=
    fun a => by rw [redSub_mk, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have h3 : ∀ a ∈ A, (n₀ * (a n₀)⁻¹) ^ 3 ∈ twoSub ψ.ker hker := by
    intro a ha
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hu ⟨a, ha⟩]
    exact (hw (redSub hker hAle ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).1
  have hfix : ∀ a ∈ A, ∀ a' ∈ A,
      (n₀ * (a n₀)⁻¹)⁻¹ * a' (n₀ * (a n₀)⁻¹) ∈ twoSub ψ.ker hker := by
    intro a ha a' ha'
    apply QuotientGroup.eq.mp
    rw [show ((a' (n₀ * (a n₀)⁻¹) : L') : L' ⧸ twoSub ψ.ker hker) =
        redSub hker hAle ⟨a', ha'⟩ ((n₀ * (a n₀)⁻¹ : L') : L' ⧸ twoSub ψ.ker hker) from
      (redSub_mk hker hAle ⟨a', ha'⟩ _).symm, hu ⟨a, ha⟩]
    exact ((hw (redSub hker hAle ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).2 _ ⟨⟨a', ha'⟩, rfl⟩).symm
  obtain ⟨z, hz, hzW⟩ :=
    exists_lift_fixed hZc hZ2 hA3 hAc (fun a ha z hz => hAle ha z hz) n₀ h3 hfix
  have hz1 : ((z : L') : L' ⧸ twoSub ψ.ker hker) = 1 := (QuotientGroup.eq_one_iff z).mpr hz
  exact ⟨n₀ * z, by rw [QuotientGroup.mk_mul, hz1, mul_one], hzW⟩

end Lift

@[expose] def NbrConcl (p : ℕ) {L' : Type} [Group L'] (K : Subgroup L')
    (A : Subgroup (MulAut L')) : Prop :=
  ∃ W : Set L',
    (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
    ∀ Y : Subgroup (MulAut L'), (∀ f ∈ Y, ∀ z ∈ K, f z ∈ K) →
      (∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
      (∀ n ∈ W, ∀ f ∈ Y, MulAut.conj n * f * (MulAut.conj n)⁻¹ ∈ Y) →
      (∀ f ∈ Y, ∀ a ∈ A, f * a * f⁻¹ ∈ A) →
      (∀ f ∈ Y, ∃ k : ℕ, ∀ a ∈ A, f ^ p ^ k * a = a * f ^ p ^ k) →
      ∀ f ∈ Y, ∀ a ∈ A, f * a = a * f

section NbrDescent

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
  (hker : ψ.ker ≤ Subgroup.center L')

theorem redSub_eq {S : Subgroup (MulAut L')} (hS : S ≤ presZ (twoSub ψ.ker hker)) (s : S) :
    redSub hker hS s = redHom (twoSub ψ.ker hker) ⟨s.1, hS s.2⟩ := rfl

theorem redSub_triple {S S' : Subgroup (MulAut L')} (hS : S ≤ presZ (twoSub ψ.ker hker))
    (hS' : S' ≤ presZ (twoSub ψ.ker hker)) (f : S) (a : S') (h : f.1 * a.1 * f.1⁻¹ ∈ S') :
    redSub hker hS' ⟨f.1 * a.1 * f.1⁻¹, h⟩ =
      redSub hker hS f * redSub hker hS' a * (redSub hker hS f)⁻¹ := by
  have : redSub hker hS' ⟨f.1 * a.1 * f.1⁻¹, h⟩ = redHom (twoSub ψ.ker hker)
      (⟨f.1, hS f.2⟩ * ⟨a.1, hS' a.2⟩ * ⟨f.1, hS f.2⟩⁻¹) := rfl
  rw [this, map_mul, map_mul, map_inv]
  rfl

theorem redSub_conj_triple {S : Subgroup (MulAut L')} (hS : S ≤ presZ (twoSub ψ.ker hker))
    (n : L') (a : S) (h : MulAut.conj n * a.1 * (MulAut.conj n)⁻¹ ∈ S) :
    redSub hker hS ⟨MulAut.conj n * a.1 * (MulAut.conj n)⁻¹, h⟩ =
      MulAut.conj (n : L' ⧸ twoSub ψ.ker hker) * redSub hker hS a *
        (MulAut.conj (n : L' ⧸ twoSub ψ.ker hker))⁻¹ := by
  have : redSub hker hS ⟨MulAut.conj n * a.1 * (MulAut.conj n)⁻¹, h⟩ = redHom (twoSub ψ.ker hker)
      (conjP _ n * ⟨a.1, hS a.2⟩ * (conjP _ n)⁻¹) := rfl
  rw [this, map_mul, map_mul, map_inv, redHom_conjP]
  rfl

include hker in
theorem nbrConcl_descent (hψ : Function.Surjective ψ) (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) {I : Set (MulAut R)}
    (hAI : ∀ a ∈ A, ∃ x ∈ I, ∀ l : L', x (ψ l) = ψ (a l)) (hsc : GGTorusSelfCent 3 A)
    (H : ∀ (L₁ : Type) [Group L₁] [Finite L₁] (ψ₁ : L₁ →* R), Function.Surjective ψ₁ →
      ψ₁.ker ≤ Subgroup.center L₁ → commutator L₁ = ⊤ → Odd (Nat.card ψ₁.ker) →
      ∀ A₁ : Subgroup (MulAut L₁), CFSG.Open.IsElemAbelian 3 A₁ →
        (∀ a ∈ A₁, ∃ x ∈ I, ∀ l : L₁, x (ψ₁ l) = ψ₁ (a l)) → Nat.card A₁ = Nat.card A →
        GGTorusSelfCent 3 A₁ → NbrConcl 3 ψ₁.ker A₁) :
    NbrConcl 3 ψ.ker A := by
  classical
  have hAle : A ≤ presZ (twoSub ψ.ker hker) := fun a ha =>
    mem_presZ_of_ker hker fun z hz => preserves_ker (hAI a ha) hz
  obtain ⟨W₁, hW₁, hY₁⟩ := H (L' ⧸ twoSub ψ.ker hker) (psi1 hker) (psi1_surjective hker hψ)
    (psi1_ker_central hker) (commutator_quot hker hperf) (odd_card_ker_psi1 hker)
    (redSub hker hAle).range (isElemAbelian_range_redSub hker hAle hA)
    (redSub_hAI hker hAle hAI) (card_range_redSub hker hAle hperf) (selfCent_quot hker hA hAle hsc)
  refine ⟨{n | (∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      (n : L' ⧸ twoSub ψ.ker hker) ∈ W₁}, fun n hn => hn.1, ?_⟩
  intro Y hYK hWA hWY hYA hYp
  have hYle : Y ≤ presZ (twoSub ψ.ker hker) := fun f hf => mem_presZ_of_ker hker (hYK f hf)
  have key := hY₁ (redSub hker hYle).range ?_ ?_ ?_ ?_ ?_
  · intro f hf a ha
    have h1 := key _ ⟨⟨f, hf⟩, rfl⟩ _ ⟨⟨a, ha⟩, rfl⟩
    have h2 : (⟨f, hYle hf⟩ : presZ (twoSub ψ.ker hker)) * ⟨a, hAle ha⟩ =
        ⟨a, hAle ha⟩ * ⟨f, hYle hf⟩ := by
      refine redHom_injective _ (twoSub_le_center hker) hperf ?_
      rw [map_mul, map_mul]
      exact h1
    exact congrArg Subtype.val h2
  · rintro _ ⟨f, rfl⟩ z₁ hz₁
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z₁
    rw [redSub_mk]
    rw [mem_ker_psi1] at hz₁ ⊢
    exact hYK f.1 f.2 z hz₁
  · intro w hw a₁ ha₁
    obtain ⟨n, rfl, hn2⟩ := exists_lift_W hker hA hAle (hW₁ w hw)
    obtain ⟨a, rfl⟩ := ha₁
    have h1 := hWA n ⟨hn2, hw⟩ a.1 a.2
    exact ⟨⟨_, h1⟩, redSub_conj_triple hker hAle n a h1⟩
  · intro w hw f₁ hf₁
    obtain ⟨n, rfl, hn2⟩ := exists_lift_W hker hA hAle (hW₁ w hw)
    obtain ⟨f, rfl⟩ := hf₁
    have h1 := hWY n ⟨hn2, hw⟩ f.1 f.2
    exact ⟨⟨_, h1⟩, redSub_conj_triple hker hYle n f h1⟩
  · rintro _ ⟨f, rfl⟩ _ ⟨a, rfl⟩
    have h1 := hYA f.1 f.2 a.1 a.2
    exact ⟨⟨_, h1⟩, redSub_triple hker hYle hAle f a h1⟩
  · rintro _ ⟨f, rfl⟩
    obtain ⟨k, hk⟩ := hYp f.1 f.2
    refine ⟨k, ?_⟩
    rintro _ ⟨a, rfl⟩
    have e : (⟨f.1, hYle f.2⟩ : presZ (twoSub ψ.ker hker)) ^ 3 ^ k * ⟨a.1, hAle a.2⟩ =
        ⟨a.1, hAle a.2⟩ * (⟨f.1, hYle f.2⟩ : presZ (twoSub ψ.ker hker)) ^ 3 ^ k :=
      Subtype.ext (hk a.1 a.2)
    show redHom (twoSub ψ.ker hker) ⟨f.1, hYle f.2⟩ ^ 3 ^ k *
        redHom (twoSub ψ.ker hker) ⟨a.1, hAle a.2⟩ =
      redHom (twoSub ψ.ker hker) ⟨a.1, hAle a.2⟩ *
        redHom (twoSub ψ.ker hker) ⟨f.1, hYle f.2⟩ ^ 3 ^ k
    rw [← map_pow, ← map_mul, ← map_mul, e]

end NbrDescent

@[expose] def ModConcl (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∃ (H : Subgroup (MulAut L')) (W : Set L'), H ≤ A ∧ H ≠ ⊥ ∧ Nat.card A ≤ p * Nat.card H ∧
    (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∀ h ∈ H, MulAut.conj n * h * (MulAut.conj n)⁻¹ ∈ H) ∧
    (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
    ∀ A' : Subgroup (MulAut L'), A' ≤ A → A' ≠ ⊥ →
      (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → H ≤ A'

section ModDescent

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
  (hker : ψ.ker ≤ Subgroup.center L')

include hker in
theorem modConcl_descent (hψ : Function.Surjective ψ) (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) {I : Set (MulAut R)}
    (hAI : ∀ a ∈ A, ∃ x ∈ I, ∀ l : L', x (ψ l) = ψ (a l)) (hsc : GGTorusSelfCent 3 A)
    (H : ∀ (L₁ : Type) [Group L₁] [Finite L₁] (ψ₁ : L₁ →* R), Function.Surjective ψ₁ →
      ψ₁.ker ≤ Subgroup.center L₁ → commutator L₁ = ⊤ → Odd (Nat.card ψ₁.ker) →
      ∀ A₁ : Subgroup (MulAut L₁), CFSG.Open.IsElemAbelian 3 A₁ →
        (∀ a ∈ A₁, ∃ x ∈ I, ∀ l : L₁, x (ψ₁ l) = ψ₁ (a l)) → Nat.card A₁ = Nat.card A →
        GGTorusSelfCent 3 A₁ → ModConcl 3 A₁) :
    ModConcl 3 A := by
  classical
  have hAle : A ≤ presZ (twoSub ψ.ker hker) := fun a ha =>
    mem_presZ_of_ker hker fun z hz => preserves_ker (hAI a ha) hz
  have hρinj := redSub_injective hker hAle hperf
  haveI : Finite (MulAut (L' ⧸ twoSub ψ.ker hker)) :=
    Finite.of_injective (fun φ : MulAut (L' ⧸ twoSub ψ.ker hker) =>
      (φ : L' ⧸ twoSub ψ.ker hker → L' ⧸ twoSub ψ.ker hker)) DFunLike.coe_injective
  obtain ⟨H₁, W₁, hH₁A, hH₁ne, hH₁card, hH₁inv, hW₁, hH₁irr⟩ :=
    H (L' ⧸ twoSub ψ.ker hker) (psi1 hker) (psi1_surjective hker hψ)
      (psi1_ker_central hker) (commutator_quot hker hperf) (odd_card_ker_psi1 hker)
      (redSub hker hAle).range (isElemAbelian_range_redSub hker hAle hA)
      (redSub_hAI hker hAle hAI) (card_range_redSub hker hAle hperf)
      (selfCent_quot hker hA hAle hsc)
  set Hc : Subgroup A := H₁.comap (redSub hker hAle) with hHc
  have hcardHc : Nat.card Hc = Nat.card H₁ := by
    have h1 : Hc.map (redSub hker hAle) = H₁ := Subgroup.map_comap_eq_self hH₁A
    rw [← Subgroup.card_map_of_injective hρinj, h1]
  refine ⟨Hc.map A.subtype, {n | (∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧
      ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧ (n : L' ⧸ twoSub ψ.ker hker) ∈ W₁},
    Subgroup.map_subtype_le _, ?_, ?_, ?_, fun n hn => hn.1, ?_⟩
  · intro hbot
    obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hH₁ne
    obtain ⟨a, ha⟩ := hH₁A hx
    have haHc : a ∈ Hc := by
      show redSub hker hAle a ∈ H₁
      rw [ha]
      exact hx
    have h1 : a.1 ∈ Hc.map A.subtype := ⟨a, haHc, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have ha1 : a = 1 := Subtype.ext h1
    apply hx1
    apply Subtype.ext
    show x = 1
    rw [← ha, ha1, map_one]
  · have h1 : Nat.card (Hc.map A.subtype) = Nat.card Hc :=
      Subgroup.card_map_of_injective A.subtype_injective
    rw [h1, hcardHc, ← card_range_redSub hker hAle hperf]
    exact hH₁card
  · intro n hn h hh
    obtain ⟨a, haHc, rfl⟩ := hh
    have hconjA : MulAut.conj n * a.1 * (MulAut.conj n)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hn a.1).mp a.2
    have hnorm₁ : MulAut.conj (n : L' ⧸ twoSub ψ.ker hker) ∈
        Subgroup.normalizer ((redSub hker hAle).range : Set (MulAut (L' ⧸ twoSub ψ.ker hker))) := by
      refine Subgroup.mem_normalizer_fintype fun a₁ ha₁ => ?_
      obtain ⟨b, rfl⟩ := ha₁
      have h1 := (Subgroup.mem_normalizer_iff.mp hn b.1).mp b.2
      exact ⟨⟨_, h1⟩, redSub_conj_triple hker hAle n b h1⟩
    refine ⟨⟨_, hconjA⟩, ?_, rfl⟩
    show redSub hker hAle ⟨_, hconjA⟩ ∈ H₁
    rw [redSub_conj_triple hker hAle n a hconjA]
    exact hH₁inv (n : L' ⧸ twoSub ψ.ker hker) hnorm₁ _ haHc
  · intro A' hA'A hA'ne hinv
    set A'₁ : Subgroup (MulAut (L' ⧸ twoSub ψ.ker hker)) :=
      (A'.subgroupOf A).map (redSub hker hAle) with hA'₁
    have hA'₁le : A'₁ ≤ (redSub hker hAle).range := Subgroup.map_le_range _ _
    have hA'₁ne : A'₁ ≠ ⊥ := by
      intro hbot
      obtain ⟨⟨a, haA'⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA'ne
      have h1 : redSub hker hAle ⟨a, hA'A haA'⟩ ∈ A'₁ :=
        ⟨⟨a, hA'A haA'⟩, Subgroup.mem_subgroupOf.mpr haA', rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 := hρinj (h1.trans (map_one (redSub hker hAle)).symm)
      have h3 : a = 1 := congrArg Subtype.val h2
      exact ha1 (Subtype.ext h3)
    have hinv₁ : ∀ w ∈ W₁, ∀ a ∈ A'₁, MulAut.conj w * a * (MulAut.conj w)⁻¹ ∈ A'₁ := by
      intro w hw a₁ ha₁
      obtain ⟨n, rfl, hn2⟩ := exists_lift_W hker hA hAle (hW₁ w hw)
      obtain ⟨a, haA', rfl⟩ := ha₁
      have haA'' : a.1 ∈ A' := Subgroup.mem_subgroupOf.mp haA'
      have h1 := hinv n ⟨hn2, hw⟩ a.1 haA''
      have h2 : MulAut.conj n * a.1 * (MulAut.conj n)⁻¹ ∈ A := hA'A h1
      exact ⟨⟨_, h2⟩, Subgroup.mem_subgroupOf.mpr h1, redSub_conj_triple hker hAle n a h2⟩
    have hirr := hH₁irr A'₁ hA'₁le hA'₁ne hinv₁
    rintro _ ⟨a, haHc, rfl⟩
    obtain ⟨b, hbA', hb⟩ := hirr (show redSub hker hAle a ∈ H₁ from haHc)
    have hba : b = a := hρinj hb
    subst hba
    exact Subgroup.mem_subgroupOf.mp hbA'

end ModDescent

end CFSG.StandardType.U63TB

end
