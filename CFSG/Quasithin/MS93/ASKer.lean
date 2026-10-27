module

public import CFSG.Quasithin.MS93.SkHyp
public import CFSG.Quasithin.MS93.ASGroup
public import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commute_of_commutator_mem {z : G} (hodd : Odd (orderOf z)) {A B : Subgroup G}
    (hA : ∀ a ∈ A, z * a = a * z) (hA2 : ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k = 1)
    (hB : ∀ b ∈ B, z * b * z⁻¹ * b⁻¹ ∈ A) : ∀ b ∈ B, z * b = b * z := by
  intro b hb
  set c := z * b * z⁻¹ * b⁻¹ with hc
  have hcA := hB b hb
  have hc1 := eq_one_of_conj_eq_mul (x := b) (hA c hcA) (by rw [hc]; group) hodd (hA2 c hcA)
  have : z * b * z⁻¹ = b := by
    calc z * b * z⁻¹ = z * b * z⁻¹ * b⁻¹ * b := by group
      _ = b := by rw [← hc, hc1, one_mul]
  calc z * b = z * b * z⁻¹ * z := by group
    _ = b * z := by rw [this]

variable [Finite G]

theorem eq_one_of_odd_of_commute {M L : Subgroup G} (hC : CharTwo M) (hLM : L ≤ M)
    {z : G} (hz : z ∈ L) (hodd : Odd (orderOf z))
    (hV : ∀ v ∈ ⁅pCoreOf 2 M, L⁆, z * v = v * z) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have h2elt : ∀ c ∈ pCoreOf 2 M, ∃ k : ℕ, c ^ 2 ^ k = 1 := fun c hc => by
    obtain ⟨k, hk⟩ := hQ2 ⟨c, hc⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hVQ : ⁅pCoreOf 2 M, L⁆ ≤ pCoreOf 2 M := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hLM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
  have hzQ : ∀ x ∈ pCoreOf 2 M, z * x = x * z :=
    commute_of_commutator_mem hodd hV (fun a ha => h2elt a (hVQ ha)) fun x hx => by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hz hx
  have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => (hzQ x hx).symm
  obtain ⟨k, hk⟩ := h2elt z (hC ⟨hLM hz, hzC⟩)
  have hd2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf z) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd2 dvd_rfl))

theorem isPGroup_of_odd_eq_one {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (h : ∀ k ∈ K, Odd (orderOf k) → k = 1) : IsPGroup 2 K := by
  rintro ⟨k, hk⟩
  obtain ⟨a, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  refine ⟨a, Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  apply h _ (K.pow_mem hk _)
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, he⟩, he,
    Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  exact hm

theorem ker_le_pCore_of_odd {L : Subgroup G} {Γ : Type*} [Group Γ] (α : ↥L →* Γ)
    (h : ∀ ℓ : ↥L, α ℓ = 1 → Odd (orderOf ℓ) → ℓ = 1) : α.ker ≤ CFSG.pCore 2 ↥L :=
  le_sSup ⟨MonoidHom.normal_ker α, isPGroup_of_odd_eq_one fun k hk hodd => h k hk hodd⟩

theorem pCore_le_ker_of_surjective {L : Subgroup G} {Γ : Type*} [Group Γ] (α : ↥L →* Γ)
    (hα : Function.Surjective α)
    (hΓ : ∀ N : Subgroup Γ, N.Normal → IsPGroup 2 N → N = ⊥) : CFSG.pCore 2 ↥L ≤ α.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hN := hΓ ((CFSG.pCore 2 ↥L).map α) (Subgroup.Normal.map inferInstance α hα)
    ((isPGroup_cfsgPCore ↥L).map α)
  exact (Subgroup.map_eq_bot_iff _).mp hN

theorem blockU_eq {M T L : Subgroup G} (h : PUHyp M T L) : blockU L = Vq M L :=
  (commutator_eq_blockU h.L_le h.le_normalizer h.perfect).symm

theorem blockZ_eq {M T L : Subgroup G} (h : PUHyp M T L) :
    blockZ L = Vq M L ⊓ Subgroup.centralizer (L : Set G) := by
  rw [blockZ, blockU_eq h]

theorem charTwo_L {M T L : Subgroup G} (h : PUHyp M T L) : CharTwo L :=
  CharTwo.of_normal h.charTwo h.L_le
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer)

theorem eq_top_of_isPGroup_quot {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (N : Subgroup X) [N.Normal] (h : IsPGroup 2 (X ⧸ N)) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← QuotientGroup.subsingleton_iff]
  by_contra hnt
  rw [not_subsingleton_iff_nontrivial] at hnt
  have : Group.IsNilpotent (X ⧸ N) := h.isNilpotent
  exact Group.IsPerfect.not_isSolvable (X ⧸ N) inferInstance

theorem isShort2_of {M T L : Subgroup G} (h : PUHyp M T L) (hVX : Vq M L ≤ Xq M)
    (hlt : Vq M L ⊓ Subgroup.centralizer (L : Set G) < Vq M L)
    (hirr : ∀ W : Subgroup G, Vq M L ⊓ Subgroup.centralizer (L : Set G) ≤ W → W ≤ Vq M L →
      L ≤ Subgroup.normalizer (W : Set G) →
        W = Vq M L ⊓ Subgroup.centralizer (L : Set G) ∨ W = Vq M L) :
    IsShort2 L := by
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
  refine ⟨fun N _ hN => eq_top_of_isPGroup_quot N hN, charTwo_L h, ⟨?_, ?_⟩,
    Or.inl h.quasisimple, ?_⟩
  · rw [blockU_eq h]
    refine le_inf (commutator_le_pCoreOf h.L_le h.le_normalizer) ?_
    refine hVX.trans ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ : y ∈ pCoreOf 2 M := pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer hy
    exact Subgroup.mem_centralizer_iff.mp
      (A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ hx)) y hyQ
  · intro x hx
    rw [blockU_eq h] at hx
    exact A4.sq_eq_one_of_mem_omegaOneCenterOf (hVX hx)
  · rw [blockZ_eq h, blockU_eq h]
    exact ⟨hlt, hirr⟩

omit [Finite G] in
theorem eq_or_eq_of_section {L V Z : Subgroup G} {B : Type*} [Group B] (β : ↥V →* B)
    (hker : β.ker = Z.subgroupOf V) (act : ↥L → B → B)
    (hact : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ → β v = act ℓ (β u))
    (hirr : ∀ Y : Subgroup B, (∀ (ℓ : ↥L) (y : B), y ∈ Y → act ℓ y ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {W : Subgroup G} (hZW : Z ≤ W) (hWV : W ≤ V)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : W = Z ∨ W = V := by
  set Y : Subgroup B := (W.subgroupOf V).map β with hY
  have hinv : ∀ (ℓ : ↥L) (y : B), y ∈ Y → act ℓ y ∈ Y := by
    rintro ℓ y ⟨u, hu, rfl⟩
    replace hu : (u : G) ∈ W := hu
    have hv : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV ℓ.2) u).mp u.2
    have hvW : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hLW ℓ.2) u).mp hu
    refine ⟨⟨_, hv⟩, Subgroup.mem_subgroupOf.mpr hvW, ?_⟩
    exact hact ℓ u ⟨_, hv⟩ rfl
  rcases hirr Y hinv with hbot | htop
  · left
    refine le_antisymm (fun w hw => ?_) hZW
    have hβw : β ⟨w, hWV hw⟩ ∈ Y := ⟨⟨w, hWV hw⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hβw
    have : (⟨w, hWV hw⟩ : ↥V) ∈ β.ker := hβw
    rw [hker, Subgroup.mem_subgroupOf] at this
    exact this
  · right
    refine le_antisymm hWV fun v hv => ?_
    have hβv : β ⟨v, hv⟩ ∈ Y := htop ▸ Subgroup.mem_top _
    obtain ⟨w, hw, hwv⟩ := hβv
    replace hw : (w : G) ∈ W := hw
    have hk : w⁻¹ * ⟨v, hv⟩ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwv, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hk
    have hvw : v = (w : G) * ((w : G)⁻¹ * v) := by group
    rw [hvw]
    exact W.mul_mem hw (hZW (by simpa using hk))

end CFSG.Quasithin.MS93
