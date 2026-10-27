module

public import CFSG.Quasithin.Background.RonanE628RModule
public import CFSG.Quasithin.Background.RonanE628ROver
public import CFSG.Quasithin.Background.E6SevenTwoA5
public import CFSG.Quasithin.Background.GoldschmidtTDC111Main
public import CFSG.Quasithin.H13.VolIC113c

public section

namespace CFSG.Quasithin.RonanE628

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open Equiv

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_normalizer_sup {H T L : Subgroup G} (hTH : IsSylowTwoOf T H)
    (hL : IsBlock2 H L) :
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G)) (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G))) := by
  have hTL : IsSylowTwoOf (T ⊓ L) L := E6.isSylowTwoOf_inf_of_isBlock2 hTH hL
  have hT'2 : IsPGroup 2 (T ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) :=
    hTH.2.1.to_le inf_le_left
  have h1 : T ⊓ L ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) : Set G) := by
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg.1,
      Subgroup.le_normalizer (Subgroup.le_normalizer hg.2)⟩
  have := F1.isSylowTwoOf_sup_sup hTL hT'2 inf_le_right h1
  have e : (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ (T ⊓ L) = T ⊓ Subgroup.normalizer (L : Set G) :=
    sup_eq_left.2 (le_inf inf_le_left (inf_le_right.trans Subgroup.le_normalizer))
  rw [e, sup_comm] at this
  exact this


theorem false_of_alt5Block {H T M V L : Subgroup G}
    (hTH : IsSylowTwoOf T H) (hL : IsBlock2 H L) (hA5 : IsAltType L 5)
    (hTM : T ≤ M) (hLM : ¬ L ≤ M)
    (hVe : IsElemAbelian 2 V) (hV3 : 3 ≤ Nat.card V) (hVT : V ≤ T)
    (hVO : V ≤ pCoreOf 2 H)
    (hC : ∀ v ∈ V, v ≠ 1 → ∀ x : G, x * v = v * x → x ∈ M) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLsh : IsShort2 L := hL.1
  have hZ : blockZ L = ⊥ := AppC.blockZ_eq_bot_of_alt5 hLsh hA5
  set T' : Subgroup G := T ⊓ Subgroup.normalizer (L : Set G) with hT'def
  have hT'T : T' ≤ T := inf_le_left
  have hT'N : T' ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hTL : IsSylowTwoOf (T ⊓ L) L := E6.isSylowTwoOf_inf_of_isBlock2 hTH hL
  have hT'syl : IsSylowTwoOf T' (L ⊔ T') := isSylowTwoOf_normalizer_sup hTH hL
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := fun v hv =>
    TDC111.mem_normalizer_of_mem_pCoreOf hL (hVO hv)
  have hVT' : V ≤ T' := le_inf hVT hVN
  have hLT'H : L ⊔ T' ≤ H := sup_le hL.2.1 (hT'T.trans hTH.1)
  obtain ⟨hQ, hUC, -, -, -, -⟩ :=
    (H13.VolI.asC113c_holds G L T' hT'syl hT'N hLsh 5 (Or.inr rfl) hA5)
  have hVQ : V ≤ pCoreOf 2 (L ⊔ T') := by
    have hW : pCoreOf 2 H ⊓ (L ⊔ T') ≤ pCoreOf 2 (L ⊔ T') := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left)
      intro y hy
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, Subgroup.le_normalizer hy⟩
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hLT'H hy)
    exact fun v hv => hW ⟨hVO hv, (le_sup_right : T' ≤ L ⊔ T') (hVT' hv)⟩
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLsh).trans (C1.blockQ_le L)
  have hcomm : ∀ a ∈ blockU L, ∀ b ∈ T' ⊓ Subgroup.centralizer (L : Set G), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb.2 a (hUL ha)
  have hdecomp : ∀ v ∈ V, ∃ u ∈ blockU L, ∃ c ∈ T' ⊓ Subgroup.centralizer (L : Set G),
      v = u * c := by
    intro v hv
    have : v ∈ blockU L ⊔ (T' ⊓ Subgroup.centralizer (L : Set G)) := hQ ▸ hVQ hv
    exact TDC111.mem_sup_of_commute' hcomm this
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ : ∃ a ∈ V, ∃ b ∈ V, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
    have h3 : 2 < (V : Set G).ncard := by
      have := Nat.card_coe_set_eq (V : Set G)
      exact lt_of_lt_of_le (by norm_num) (this ▸ hV3)
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 h3
    by_cases hx1 : x = 1
    · exact ⟨y, hy, z, hz, fun h => hxy (hx1.trans h.symm), fun h => hxz (hx1.trans h.symm), hyz⟩
    by_cases hy1 : y = 1
    · exact ⟨x, hx, z, hz, hx1, fun h => hyz (hy1.trans h.symm), hxz⟩
    · exact ⟨x, hx, y, hy, hx1, hy1, hxy⟩
  have hsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := hVe.2 v hv
    rwa [sq] at this
  have hUsq : ∀ u ∈ blockU L, u * u = 1 := fun u hu => by
    have := hLsh.2.2.1.2 u hu
    rwa [sq] at this
  have hno : ∀ v ∈ V, v ≠ 1 → v ∈ Subgroup.centralizer (L : Set G) → False := by
    intro v hv hv1 hvc
    apply hLM
    intro x hx
    exact hC v hv hv1 x (Subgroup.mem_centralizer_iff.1 hvc x hx)
  obtain ⟨u₁, hu₁, c₁, hc₁, hac⟩ := hdecomp a ha
  obtain ⟨u₂, hu₂, c₂, hc₂, hbc⟩ := hdecomp b hb
  have hc₁L : c₁ ∈ Subgroup.centralizer (L : Set G) := hc₁.2
  have hc₂L : c₂ ∈ Subgroup.centralizer (L : Set G) := hc₂.2
  have hu₁1 : u₁ ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hac
    exact hno a ha ha1 (hac ▸ hc₁L)
  have hu₂1 : u₂ ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hbc
    exact hno b hb hb1 (hbc ▸ hc₂L)
  have hab' : a * b ∈ V := V.mul_mem ha hb
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have h' : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h', inv_eq_of_mul_eq_one_right (hsq b hb)]
  have hu12 : u₁ * u₂ ≠ 1 := by
    intro h1
    have hmul : a * b = c₁ * c₂ := by
      have h2 := hcomm u₂ hu₂ c₁ hc₁
      calc a * b = (u₁ * c₁) * (u₂ * c₂) := by rw [← hac, ← hbc]
        _ = u₁ * (c₁ * u₂) * c₂ := by group
        _ = u₁ * (u₂ * c₁) * c₂ := by rw [h2]
        _ = u₁ * u₂ * (c₁ * c₂) := by group
        _ = c₁ * c₂ := by rw [h1, one_mul]
    exact hno (a * b) hab' hab1 (hmul ▸ (Subgroup.mul_mem _ hc₁L hc₂L))
  have hu12e : u₁ ≠ u₂ := fun h => hu12 (h ▸ hUsq u₁ hu₁)
  obtain ⟨α, hα, hαk, β, hβs, hβk, hβe⟩ := hA5
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  let vec : ↥(blockU L) → (Fin 5 → ZMod 2) := fun x =>
    ((Multiplicative.toAdd (β x) : evenWeight 5) : Fin 5 → ZMod 2)
  have vec_sum : ∀ x, ∑ i, vec x i = 0 := fun x => by
    have h : ((Multiplicative.toAdd (β x) : evenWeight 5) : Fin 5 → ZMod 2) ∈ evenWeight 5 :=
      (Multiplicative.toAdd (β x)).2
    exact AddMonoidHom.mem_ker.1 h
  have vec_mul : ∀ x y, vec (x * y) = vec x + vec y := fun x y => by
    simp [vec]
  have vec_inj : ∀ x y, vec x = vec y → x = y := fun x y h => by
    apply hβinj
    apply Multiplicative.toAdd.injective
    exact Subtype.ext h
  have vec_ne : ∀ x, x ≠ 1 → vec x ≠ 0 := fun x hx h0 => by
    apply hx
    apply hβinj
    rw [map_one]
    apply Multiplicative.toAdd.injective
    exact Subtype.ext h0
  have hO2L : pCoreOf 2 L ≤ T' := by
    have hnorm : L ⊔ T' ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
      refine sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) ?_
      exact hT'N.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
    have h1 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T') :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) hnorm
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact h1.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT'syl)
  have hker : ∀ x : ↥L, α x = 1 → (x : G) ∈ T := fun x hx => by
    have hxk : x ∈ CFSG.pCore 2 ↥L := by
      rw [← hαk]
      exact MonoidHom.mem_ker.2 hx
    exact hT'T (hO2L (Subgroup.mem_map.2 ⟨x, hxk, rfl⟩))
  obtain ⟨p, hp⟩ := ModF.exists_fixed (α := α) (S := T) hTL
  have hkl := ModF.imgS_eq_klein hα hker hTL hp
  have hkerM : ∀ x : ↥L, α x = 1 → (x : G) ∈ M := fun x hx => hTM (hker x hx)
  have hkY : ∀ g : Perm (Fin 5), g * g = 1 → Perm.sign g = 1 → g p = p →
      g ∈ ModF.imgS L M α := by
    intro g h2 hs hgp
    have hgk : g ∈ ModF.klein p := by
      simp [ModF.klein, h2, hs, hgp]
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ((hkl g).2 hgk)
    refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 ⟨hTM (Subgroup.mem_subgroupOf.1 hy).1, y.2⟩
  have hsign3 : ∀ σ : Perm (Fin 5), orderOf σ = 3 → Perm.sign σ = 1 := by
    intro σ hσ
    have hpow : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
    have h1 : Perm.sign σ ^ 3 = 1 := by rw [← map_pow, hpow, map_one]
    rcases Int.units_eq_one_or (Perm.sign σ) with h2 | h2
    · exact h2
    · rw [h2] at h1
      exact absurd h1 (by decide)
  have hclaim : ∃ (u : G) (hu : u ∈ blockU L) (c : G), c ∈ Subgroup.centralizer (L : Set G) ∧
      u * c ∈ V ∧ u * c ≠ 1 ∧ ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ σ p ≠ p ∧
        (fun i => vec ⟨u, hu⟩ (σ i)) = vec ⟨u, hu⟩ := by
    obtain ⟨w, hw, σ, hσ3, hσp, hσw⟩ := a5Module_good_at p (vec ⟨u₁, hu₁⟩) (vec ⟨u₂, hu₂⟩)
      (vec_sum _) (vec_sum _) (vec_ne _ (fun h => hu₁1 (congrArg Subtype.val h)))
      (vec_ne _ (fun h => hu₂1 (congrArg Subtype.val h)))
      (fun h => hu12e (congrArg Subtype.val (vec_inj _ _ h)))
    have hs := hsign3 σ hσ3
    rcases hw with rfl | rfl | rfl
    · exact ⟨u₁, hu₁, c₁, hc₁L, hac ▸ ha, hac ▸ ha1, σ, hs, hσp, hσw⟩
    · exact ⟨u₂, hu₂, c₂, hc₂L, hbc ▸ hb, hbc ▸ hb1, σ, hs, hσp, hσw⟩
    · have hmul : (⟨u₁ * u₂, Subgroup.mul_mem _ hu₁ hu₂⟩ : ↥(blockU L)) =
          ⟨u₁, hu₁⟩ * ⟨u₂, hu₂⟩ := rfl
      refine ⟨u₁ * u₂, Subgroup.mul_mem _ hu₁ hu₂, c₁ * c₂, Subgroup.mul_mem _ hc₁L hc₂L, ?_, ?_,
        σ, hs, hσp, ?_⟩
      · have : a * b = (u₁ * u₂) * (c₁ * c₂) := by
          have h2 := hcomm u₂ hu₂ c₁ hc₁
          calc a * b = (u₁ * c₁) * (u₂ * c₂) := by rw [← hac, ← hbc]
            _ = u₁ * (c₁ * u₂) * c₂ := by group
            _ = u₁ * (u₂ * c₁) * c₂ := by rw [h2]
            _ = u₁ * u₂ * (c₁ * c₂) := by group
        rw [← this]
        exact hab'
      · have : a * b = (u₁ * u₂) * (c₁ * c₂) := by
          have h2 := hcomm u₂ hu₂ c₁ hc₁
          calc a * b = (u₁ * c₁) * (u₂ * c₂) := by rw [← hac, ← hbc]
            _ = u₁ * (c₁ * u₂) * c₂ := by group
            _ = u₁ * (u₂ * c₁) * c₂ := by rw [h2]
            _ = u₁ * u₂ * (c₁ * c₂) := by group
        rw [← this]
        exact hab1
      · rw [hmul, vec_mul]
        exact hσw
  obtain ⟨u, hu, c, hcL, hvV, hv1, σ, hσs, hσp, hσw⟩ := hclaim
  obtain ⟨x, hx⟩ := hα ⟨σ, Perm.mem_alternatingGroup.2 hσs⟩
  have hαx : ((α x : alternatingGroup (Fin 5)) : Perm (Fin 5)) = σ := congrArg Subtype.val hx
  have hxu : (x : G) * u * (x : G)⁻¹ = u := by
    have hu' : (x : G) * u * (x : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.1 (C1.le_normalizer_blockU L x.2) u).1 hu
    have he := hβe x ⟨u, hu⟩ ⟨_, hu'⟩ rfl
    have heq : vec ⟨(x : G) * u * (x : G)⁻¹, hu'⟩ = vec ⟨u, hu⟩ := by
      funext i
      rw [show vec ⟨(x : G) * u * (x : G)⁻¹, hu'⟩ i =
        vec ⟨u, hu⟩ (((α x : alternatingGroup (Fin 5)) : Perm (Fin 5))⁻¹ i) from he i, hαx]
      have h1 := congrFun hσw (σ⁻¹ i)
      simpa using h1.symm
    exact congrArg Subtype.val (vec_inj _ _ heq)
  have hxc : (x : G) * c = c * (x : G) := Subgroup.mem_centralizer_iff.1 hcL x x.2
  have hxv : (x : G) * (u * c) = (u * c) * (x : G) := by
    calc (x : G) * (u * c) = ((x : G) * u * (x : G)⁻¹) * ((x : G) * c) := by group
      _ = u * (c * (x : G)) := by rw [hxu, hxc]
      _ = (u * c) * (x : G) := by group
  have hxM : (x : G) ∈ M := hC (u * c) hvV hv1 x hxv
  have hxY : ModF.toPerm α x ∈ ModF.imgS L M α := (ModF.mem_imgS_iff hkerM x).2 hxM
  have hσY : σ ∈ ModF.imgS L M α := by
    rw [ModF.toPerm_apply, hαx] at hxY
    exact hxY
  have hall := a5_overgroup p (ModF.imgS L M α) hkY hσY hσs hσp
  apply hLM
  intro y hy
  exact (ModF.mem_imgS_iff hkerM ⟨y, hy⟩).1 (hall _ (ModF.sign_toPerm ⟨y, hy⟩))

end CFSG.Quasithin.RonanE628
