module

public import CFSG.Quasithin.MS93.ASKer
public import CFSG.Quasithin.Vol2.KGNatVec
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem eq_or_eq_of_natural {L W Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥L →* ↥Γ}
    (hα : Function.Surjective α)
    (htr : ∀ x y : ι → F, x ≠ 0 → y ≠ 0 →
      ∃ γ : ↥Γ, ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec x = y)
    (h : IsSumOfNaturalModulesVia L W Z α false 1) {Y : Subgroup G} (hZY : Z ≤ Y)
    (hYW : Y ≤ W) (hLY : L ≤ Subgroup.normalizer (Y : Set G)) : Y = Z ∨ Y = W := by
  obtain ⟨hLW, -, β, -, hker, hβeq⟩ := h
  let act : ↥L → Multiplicative (Fin 1 → ι → F) → Multiplicative (Fin 1 → ι → F) :=
    fun ℓ y => Multiplicative.ofAdd fun i =>
      ((α ℓ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec (Multiplicative.toAdd y i)
  refine eq_or_eq_of_section β hker act (fun ℓ u v huv => ?_) (fun Y' hY' => ?_) hLW hZY hYW hLY
  · apply Multiplicative.toAdd.injective
    funext i
    rw [hβeq ℓ u v huv i]
    rfl
  · by_cases hbot : Y' = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨⟨y, hyY⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    have hy0 : Multiplicative.toAdd y 0 ≠ 0 := by
      intro h0
      apply hy1
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      funext i
      rw [Subsingleton.elim i 0, h0]
      rfl
    refine eq_top_iff.mpr fun z _ => ?_
    by_cases hz : Multiplicative.toAdd z 0 = 0
    · have : z = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [Subsingleton.elim i 0, hz]
        rfl
      rw [this]
      exact Y'.one_mem
    obtain ⟨γ, hγ⟩ := htr _ _ hy0 hz
    obtain ⟨ℓ, rfl⟩ := hα γ
    have hmem := hY' ℓ y hyY
    have : act ℓ y = z := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [Subsingleton.elim i 0]
      exact hγ
    rwa [this] at hmem

theorem statedSL3_transitive {F : Type} [Field F] (x y : Fin 3 → F) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F),
      ((γ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x = y := by
  obtain ⟨γ, hγ⟩ := Vol2.KGNat.exists_sl3_lin_eq x y hx hy
  exact ⟨γ, by rwa [Vol2.KGNat.linModelNat_lin] at hγ⟩

theorem statedSp2_transitive {F : Type} [Field F] (x y : Fin 2 ⊕ Fin 2 → F) (hx : x ≠ 0)
    (hy : y ≠ 0) :
    ∃ γ : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F),
      ((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec x = y := by
  obtain ⟨γ, hγ⟩ := Vol2.KGNat.exists_sp4_lin_eq x y hx hy
  exact ⟨γ, by rwa [Vol2.KGNat.linModelNat_lin] at hγ⟩

theorem eq_bot_or_eq_of_autI {L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hirr : ∀ W : Subgroup (IntMod V hV), (∀ φ ∈ autI hV L, ∀ w ∈ W, φ w ∈ W) →
      W = ⊥ ∨ W = ⊤)
    {W : Subgroup G} (hWV : W ≤ V)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = V := by
  let W' : Subgroup (IntMod V hV) :=
    { carrier := {v | v.val ∈ W}
      mul_mem' := fun {a b} ha hb => by
        show (a * b).val ∈ W
        rw [IntMod.val_mul]
        exact W.mul_mem ha hb
      one_mem' := by
        show (1 : IntMod V hV).val ∈ W
        rw [IntMod.val_one]
        exact W.one_mem
      inv_mem' := fun {a} ha => by
        show (a⁻¹).val ∈ W
        rw [IntMod.val_inv]
        exact W.inv_mem ha }
  have hinv : ∀ φ ∈ autI hV L, ∀ w ∈ W', φ w ∈ W' := by
    intro φ hφ w hw
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    show (convI hV g w).val ∈ W
    rw [convI_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp (hLW hg) _).mp hw
  rcases hirr W' hinv with hbot | htop
  · left
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxW' : (IntMod.mk hV ⟨x, hWV hx⟩) ∈ W' := hx
    rw [hbot, Subgroup.mem_bot] at hxW'
    have := congrArg IntMod.val hxW'
    rw [Subgroup.mem_bot]
    exact this
  · right
    refine le_antisymm hWV fun v hv => ?_
    have : (IntMod.mk hV ⟨v, hv⟩) ∈ W' := htop ▸ Subgroup.mem_top _
    exact this

variable [Finite G]

omit [Finite G] in
theorem commutator_mem_of_mem_ker {L V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥L →* ↥Γ}
    {k : ℕ} {dual : Bool} (h : IsSumOfNaturalModulesVia L V Z α dual k) {ℓ : ↥L} (hℓ : α ℓ = 1)
    {b : G} (hb : b ∈ V) : (ℓ : G) * b * (ℓ : G)⁻¹ * b⁻¹ ∈ Z := by
  obtain ⟨hLV, -, β, -, hker, hβeq⟩ := h
  have hv : (ℓ : G) * b * (ℓ : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV ℓ.2) b).mp hb
  have hβ : β ⟨_, hv⟩ = β ⟨b, hb⟩ := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [hβeq ℓ ⟨b, hb⟩ ⟨_, hv⟩ rfl i, hℓ]
    cases dual <;> simp [moduleAct]
  have hmem : (⟨_, hv⟩ : ↥V) * (⟨b, hb⟩ : ↥V)⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβ, mul_inv_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

theorem ker_le_pCore_of_natural {M T L Z : Subgroup G} (h : PUHyp M T L)
    (hZ : Z ≤ Subgroup.centralizer (L : Set G)) {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥L →* ↥Γ}
    {k : ℕ} {dual : Bool} (hn : IsSumOfNaturalModulesVia L (Vq M L) Z α dual k) :
    α.ker ≤ CFSG.pCore 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ker_le_pCore_of_odd α fun ℓ hℓ hodd => ?_
  have hodd' : Odd (orderOf (ℓ : G)) := by rwa [Subgroup.orderOf_coe]
  have hZV : Z ≤ Vq M L := hn.2.1
  have h2 : ∀ a ∈ Z, ∃ k : ℕ, a ^ 2 ^ k = 1 := fun a ha => by
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
      ⟨a, Vq_le_pCoreOf h.L_le (hZV ha)⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcomm := commute_of_commutator_mem hodd'
    (fun a ha => (Subgroup.mem_centralizer_iff.mp (hZ ha) ℓ ℓ.2)) h2
    (fun b hb => commutator_mem_of_mem_ker hn hℓ hb)
  exact Subtype.ext (eq_one_of_odd_of_commute h.charTwo h.L_le ℓ.2 hodd' hcomm)

theorem mem_pCoreOf_of_mem_pCore {M T L : Subgroup G} (h : PUHyp M T L) {o : ↥L}
    (ho : o ∈ CFSG.pCore 2 ↥L) : (o : G) ∈ pCoreOf 2 M := by
  refine pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer ?_
  refine ⟨o, ?_, rfl⟩
  exact ho

theorem pCore_le_ker_of_natural {M T L Z : Subgroup G} (h : PUHyp M T L) (hVX : Vq M L ≤ Xq M)
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥L →* ↥Γ} {k : ℕ} (hk : 0 < k)
    (hn : IsSumOfNaturalModulesVia L (Vq M L) Z α false k) :
    CFSG.pCore 2 ↥L ≤ α.ker := by
  obtain ⟨hLV, -, β, hβ, -, hβeq⟩ := hn
  intro o ho
  have hoQ := mem_pCoreOf_of_mem_pCore h ho
  have hcent : ∀ u : ↥(Vq M L), (o : G) * u * (o : G)⁻¹ = u := by
    intro u
    have hu := hVX u.2
    have hc := Subgroup.mem_centralizer_iff.mp
      (A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ hu)) _ hoQ
    rw [hc, mul_inv_cancel_right]
  have hfix : ∀ x : ι → F,
      ((α o : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec x = x := by
    intro x
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd fun _ => x)
    have := hβeq o u u (hcent u).symm ⟨0, hk⟩
    rw [hu] at this
    simpa [moduleAct] using this.symm
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  apply Units.ext
  show ((α o : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) = 1
  have : Matrix.toLin' ((α o : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) =
      Matrix.toLin' (1 : Matrix ι ι F) := by
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix, Matrix.one_mulVec]
  exact Matrix.toLin'.injective this

theorem isModO2Surj_of_natural {M T L Z : Subgroup G} (h : PUHyp M T L) (hVX : Vq M L ≤ Xq M)
    (hZ : Z ≤ Subgroup.centralizer (L : Set G)) {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥L →* ↥Γ}
    (hα : Function.Surjective α) (hn : IsSumOfNaturalModulesVia L (Vq M L) Z α false 1) :
    IsModO2Surj L α :=
  ⟨hα, le_antisymm (ker_le_pCore_of_natural h hZ hn) (pCore_le_ker_of_natural h hVX one_pos hn)⟩

end CFSG.Quasithin.MS93
