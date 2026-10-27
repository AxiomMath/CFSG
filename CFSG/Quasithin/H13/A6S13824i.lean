module

public import CFSG.Quasithin.Background.SmithB45Alt7Class
public import CFSG.Quasithin.Background.SmithB42Alt7Model
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.H13.A6S13824d

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped Pointwise IsMulCommutative commutatorElement

namespace A7F

theorem isQuasisimple_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X := by
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hX
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hX
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h
  · have e : X ⧸ Subgroup.center X ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup

end A7F

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace SecHyp

variable {H K X W : Subgroup G} (hs : S.SecHyp H K X W) [IsMulCommutative ↥X]
include hs

theorem nonempty_iso7 {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    Nonempty (↥(autSec (autOn K X) ⊤ (W.subgroupOf X)) ≃* alternatingGroup (Fin 7)) := by
  set LX := autSec (autOn K X) ⊤ (W.subgroupOf X) with hLX
  let φ : ↥K →* ↥LX := (hs.act.comp (Subgroup.inclusion hs.hKH)).codRestrict LX fun k =>
    (hs.mem_autSec_iff hs.hKH).2 ⟨_, k.2, rfl⟩
  have hφs : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff hs.hKH).1 hψ
    exact ⟨⟨f, hf⟩, rfl⟩
  have hker : φ.ker = α.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hαk]
    have : φ k = 1 ↔ hs.act (Subgroup.inclusion hs.hKH k) = 1 := by
      rw [← Subtype.coe_inj]
      rfl
    rw [this, hs.act_eq_one_iff]
    rfl
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)⟩

theorem ident7
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    (hirrK : XMod.IsIrrSec ↥(autSec (autOn K X) ⊤ (W.subgroupOf X))
      (⊥ : Subgroup (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))) ⊤)
    (hcard : Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) ≤ 2 ^ 12) :
    (∃ π : alternatingGroup (Fin 7) →* ↥(autSec (autOn K X) ⊤ (W.subgroupOf X)),
      (FFModel.altDn 7).RealizesVia (autSec (autOn K X) ⊤ (W.subgroupOf X)) ⊤ ⊥ π) ∨
    Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) = 16 := by
  classical
  set LX := autSec (autOn K X) ⊤ (W.subgroupOf X) with hLX
  obtain ⟨ι⟩ := hs.nonempty_iso7 hαs hαk
  have hfix : fixV LX = ⊥ := hs.fixV_eq_bot hirr
  have hirr' : ∀ J : Subgroup (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)),
      (∀ l ∈ LX, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    rcases (hirrK.2 J (fun l v hv => hJ l l.2 v hv) bot_le le_top) with h | h
    · exact Or.inl h
    · exact Or.inr h
  let _ : Module (ZMod 2) (Additive (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      have h3 : Additive.toMul (2 • x) = 1 := by
        rw [toMul_nsmul]
        exact hs.sec_pow_two _
      exact toMul_eq_one.1 h3
  rcases B45Alt7.classify ι hirr' hfix hcard with ⟨β, hβ⟩ | ⟨E, hEL, hEe, hE4, hEV⟩
  · left
    obtain ⟨π, hπ⟩ := QuasithinUnique.B42A57.realizesMod_of_equivariant
      (FFModel.altDn_isActionModel 7) QuasithinUnique.B42A57.altDn7_ker LX ι.symm.toMonoidHom
      ι.symm.surjective β fun γ s => hβ γ s
    exact ⟨π, hπ⟩
  · right
    have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hE2 : IsPGroup 2 (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) := fun y =>
      ⟨1, by rw [pow_one]; exact hs.sec_pow_two y⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE2
    have h16 := hs.card_ge_sixteen7 hαs hαk
    by_contra hne
    have hbig : 32 ≤ Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) := by
      rw [hn] at h16 hne ⊢
      have h4 : 4 ≤ n := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 (by simpa using h16)
      have h5 : 5 ≤ n := by
        by_contra h
        have : n = 4 := by omega
        exact hne (by rw [this]; norm_num)
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have hsimpL : IsSimpleGroup ↥LX := ι.isSimpleGroup
    have hcardL : Nat.card ↥LX = 2520 := by
      rw [Nat.card_congr ι.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have hnab : ∃ a b : ↥LX, a * b ≠ b * a := by
      refine ⟨ι.symm ⟨_, A7F.a7_mem⟩, ι.symm ⟨_, A7F.b7_mem⟩, fun h => ?_⟩
      have h1 := congrArg ι h
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
      exact A7F.ab7_ne_ba7 (congrArg Subtype.val h1)
    have hO2 : pCoreOf 2 LX = ⊥ := by
      have hn' : (pCoreOf 2 LX).subgroupOf LX ≤ ⊤ := le_top
      have hnorm : ((pCoreOf 2 LX).subgroupOf LX).Normal := by
        refine ⟨fun x hx g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 LX g.2) x).mp hx
        simpa using this
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pCoreOf 2 LX).subgroupOf LX) with h | h
      · rw [eq_bot_iff]
        intro x hx
        have : (⟨x, pCoreOf_le 2 LX hx⟩ : ↥LX) ∈ (pCoreOf 2 LX).subgroupOf LX :=
          Subgroup.mem_subgroupOf.2 hx
        rw [h, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
      · exfalso
        have hp : IsPGroup 2 ↥LX := by
          intro x
          have hx : x ∈ (pCoreOf 2 LX).subgroupOf LX := h ▸ Subgroup.mem_top x
          obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 LX) ⟨x, Subgroup.mem_subgroupOf.1 hx⟩
          exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
        obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hp
        rw [hcardL] at hm
        have h5 : 5 ∣ 2 ^ m := hm ▸ (by norm_num : 5 ∣ 2520)
        exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5) (by norm_num)
    have hFL : quasithinGenFitting LX = LX :=
      B1Red.quasithinGenFitting_eq_of_two_quot le_rfl (fun y hy l hl => LX.mul_mem
        (LX.mul_mem hy hl) (LX.inv_mem hy)) (A7F.isQuasisimple_of_simple hnab)
        (fun y hy => LX.pow_mem hy 2) hO2
    have C : Bridge.Alt57.Ctx LX LX 7 :=
      ⟨Or.inr rfl, ⟨ι⟩, hFL.symm, fun y hy => LX.pow_mem hy 2⟩
    have hEoff : IsFFStarOffender LX E := by
      refine ⟨hEL, ?_, hEe, fun B hBE => ?_⟩
      · intro h
        rw [h, Subgroup.card_bot] at hE4
        exact absurd hE4 (by norm_num)
      · by_cases hB1 : B = ⊥
        · rw [hB1, Subgroup.card_bot, one_mul]
          have : fixV (⊥ : Subgroup (MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)))) = ⊤ := by
            ext v; simp [mem_fixV]
          rw [this, Subgroup.card_top, hE4]
          exact hEV
        have hBe : IsElemAbelian2 B := ⟨fun a ha b hb => hEe.1 a (hBE ha) b (hBE hb),
          fun a ha => hEe.2 a (hBE ha)⟩
        obtain ⟨ι', e, hinj, hL', -⟩ := QuasithinUnique.B42A57.exists_embedding C
        have hBL : B ≤ LX := hBE.trans hEL
        have hb1 : (B.subgroupOf LX).map e ≠ ⊥ := by
          obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB1
          intro h
          have hmem : e ⟨b, hBL hb⟩ ∈ (B.subgroupOf LX).map e :=
            ⟨⟨b, hBL hb⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
          rw [h, Subgroup.mem_bot, ← map_one e] at hmem
          have := congrArg Subtype.val (hinj hmem)
          exact hb1 (Subtype.ext this)
        have hbc : ∀ x ∈ (B.subgroupOf LX).map e, ∀ y ∈ (B.subgroupOf LX).map e,
            x * y = y * x := by
          rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hBe.1 _ (Subgroup.mem_subgroupOf.1 hx) _ (Subgroup.mem_subgroupOf.1 hy))
        have hb2 : ∀ x ∈ (B.subgroupOf LX).map e, x * x = 1 := by
          rintro _ ⟨x, hx, rfl⟩
          rw [← map_mul]
          have : x * x = 1 := Subtype.ext (by
            have := hBe.2 _ (Subgroup.mem_subgroupOf.1 hx)
            simpa [pow_two] using this)
          rw [this, map_one]
        have hcardB : Nat.card ((B.subgroupOf LX).map e) = Nat.card B := by
          rw [Subgroup.card_map_of_injective hinj]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
        obtain ⟨r, f, hf, hbound, hcl⟩ := QuasithinUnique.B42A57.gen7 hb1 hbc hb2
        have hle := B42Alt7.card_le_index_pow C hirrK B ι' e hinj hL' f hf hcl
        have hBidx : Nat.card B ≤ (fixV B).index := by
          by_contra hlt
          push Not at hlt
          have hBp : IsPGroup 2 ↥B := fun x => ⟨1, Subtype.ext (by
            rw [pow_one]
            simpa using hBe.2 _ x.2)⟩
          obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hBp
          have hidvd : (fixV B).index ∣ 2 ^ n := hn ▸ Subgroup.index_dvd_card _
          obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hidvd
          rw [hb, hi] at hlt
          rw [hcardB, hb] at hbound
          rw [hi, hn] at hle
          have hib : i < b := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 hlt
          have h1 : n ≤ i * r := by
            rw [← pow_mul] at hle
            exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 hle
          have h2 : b * r ≤ 6 := by
            rw [← pow_mul] at hbound
            exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 hbound
          rw [hn] at hbig
          have h5 : 5 ≤ n := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1
            (by simpa using hbig)
          have hbE : b ≤ 2 := by
            have h1 := Subgroup.card_le_of_le hBE
            rw [hb, hE4] at h1
            exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 (by simpa using h1)
          have hr6 : r ≤ 6 := by nlinarith
          interval_cases r <;> omega
        calc Nat.card B * Nat.card (fixV B) ≤ (fixV B).index * Nat.card (fixV B) :=
              Nat.mul_le_mul_right _ hBidx
          _ = Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) := Subgroup.index_mul_card _
          _ ≤ Nat.card E * Nat.card (fixV E) := by rw [hE4]; exact hEV
    obtain ⟨M⟩ := B42Alt7.exists_symModel hs.sec_sq C hirrK hEoff hbig
    have hle : Nat.card (Perm (Fin 7)) ≤ Nat.card ↥LX :=
      Nat.card_le_card_of_injective (fun σ => (⟨M.ρ σ, M.ρ_mem σ⟩ : ↥LX)) fun a b h =>
        M.ρ_inj (congrArg Subtype.val h)
    rw [hcardL, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
    exact absurd hle (by decide)

end SecHyp

end Setting4

end CFSG.Quasithin.H13.A6
