module

public import CFSG.Quasithin.H13.A6S13828j
public import CFSG.Quasithin.Vol2.GoldschmidtKGHatA6Six
public import CFSG.Quasithin.EmptyFaithful.S1422LocTitsAct

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin CFSG.Fischer CFSG.Quasithin.Vol2.KGHat

theorem relIndex_eq_four_pow_of_hat {G : Type} [Group G] [Finite G] {L U W : Subgroup G}
    (hhat : IsHatA6 L) (hWU : W < U) (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ W)
    (hsq : ∀ a ∈ U, a * a ∈ W) (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hO2 : ∀ x ∈ pCoreOf 2 L, ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ W)
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ U → L ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = U)
    (hc : ∃ c ∈ l0 L, ∃ u ∈ U, c * u * c⁻¹ * u⁻¹ ∉ W) :
    ∃ d, 3 ∣ d ∧ W.relIndex U = 4 ^ d := by
  classical
  have hWn : ∀ u ∈ U, ∀ w ∈ W, u * w * u⁻¹ ∈ W := fun u hu w hw => by
    rw [show u * w * u⁻¹ = (u * w * u⁻¹ * w⁻¹) * w by group]
    exact W.mul_mem (hcomm u hu w (hWU.le hw)) hw
  have hN : (W.subgroupOf U).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hWn _ g.2 _ hn⟩
  set N := W.subgroupOf U with hNdef
  have hmk : ∀ x y : ↥U, (QuotientGroup.mk x : ↥U ⧸ N) = QuotientGroup.mk y ↔
      (x : G)⁻¹ * y ∈ W := fun x y => by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  let _ : CommGroup (↥U ⧸ N) :=
    { (inferInstance : Group (↥U ⧸ N)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with | H x => ?_
        induction b using QuotientGroup.induction_on with | H y => ?_
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmk]
        have h1 := hcomm _ (U.inv_mem y.2) _ (U.inv_mem x.2)
        have e : ((x * y : ↥U) : G)⁻¹ * ((y * x : ↥U) : G) =
            (y : G)⁻¹ * (x : G)⁻¹ * ((y : G)⁻¹)⁻¹ * ((x : G)⁻¹)⁻¹ := by
          push_cast; group
        rw [e]
        exact h1 }
  have hM2 : ∀ m : ↥U ⧸ N, m ^ 2 = 1 := by
    intro m
    induction m using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, pow_two]
    exact hsq _ x.2
  let _ : Module (ZMod 2) (Additive (↥U ⧸ N)) := zmod2ModuleOfExp hM2
  set ρ₀ := S1422Loc.quotAction hLU hLW with hρ₀
  set ρ₁ := (linAutHom (V := ↥U ⧸ N)).comp ρ₀ with hρ₁
  have hρ₁mk : ∀ (l : ↥L) (x : ↥U), ρ₁ l (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk (⟨(l : G) * x * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLU l.2) x).mp x.2⟩ : ↥U)) := by
    intro l x
    show autLin (ρ₀ l) (Additive.ofMul _) = _
    rw [autLin_apply, hρ₀, S1422Loc.quotAction_mk]
  have htriv : ∀ l : ↥L, (l : G) ∈ pCoreOf 2 L → ρ₁ l = 1 := by
    intro l hl
    refine LinearMap.ext fun v => ?_
    obtain ⟨m, rfl⟩ := Additive.ofMul.surjective v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective m
    rw [hρ₁mk, Module.End.one_apply]
    congr 1
    rw [hmk]
    have h1 := hO2 _ hl _ (U.inv_mem x.2)
    rw [show ((l : G) * x * (l : G)⁻¹)⁻¹ * x = (l : G) * (x : G)⁻¹ * (l : G)⁻¹ * ((x : G)⁻¹)⁻¹
      by group]
    exact h1
  have hker : CFSG.pCore 2 ↥L ≤ ρ₁.ker := fun l hl =>
    (MonoidHom.mem_ker).2 (htriv l ((mem_pCore_iff l).1 hl))
  set α := QuotientGroup.lift (CFSG.pCore 2 ↥L) ρ₁ hker with hα
  have hαmk : ∀ l : ↥L, α (QuotientGroup.mk l) = ρ₁ l := fun l => QuotientGroup.lift_mk _ _ _
  obtain ⟨c, hcl0, u₀, hu₀U, hcu₀⟩ := hc
  have hcL : c ∈ L := l0_le_L hcl0
  have hcZ : c ∈ o2Z L := oTwoRes_le _ hcl0
  set c' : ↥L := ⟨c, hcL⟩ with hc'
  set z₀ : ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk c' with hz₀
  set z := α z₀ with hzdef
  have hzc : z = ρ₁ c' := hαmk c'
  have hcomm' : ∀ l : ↥L, ρ₁ l * ρ₁ c' = ρ₁ c' * ρ₁ l := by
    intro l
    obtain ⟨-, hcl⟩ := mem_o2Z_iff.1 hcZ
    have h1 := htriv (c' * l * c'⁻¹ * l⁻¹) (hcl l l.2)
    have e : c' * l = (c' * l * c'⁻¹ * l⁻¹) * (l * c') := by group
    calc ρ₁ l * ρ₁ c' = ρ₁ (l * c') := (map_mul _ _ _).symm
      _ = ρ₁ (c' * l * c'⁻¹ * l⁻¹) * ρ₁ (l * c') := by rw [h1, one_mul]
      _ = ρ₁ (c' * l) := by rw [← map_mul, ← e]
      _ = ρ₁ c' * ρ₁ l := map_mul _ _ _
  have hαz : ∀ γ x, α γ (z x) = z (α γ x) := by
    intro γ x
    induction γ using QuotientGroup.induction_on with | H l => ?_
    rw [hαmk, hzc]
    exact LinearMap.congr_fun (hcomm' l) x
  have hz3 : ∀ w, z (z (z w)) = w := by
    have hcen : z₀ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      obtain ⟨y, hy, hyc⟩ := hcZ
      have : y = c' := Subtype.ext hyc
      rw [hz₀, ← this]
      exact hy
    have hpow : z₀ ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
        (x := ⟨z₀, hcen⟩)
      rw [hhat.2.1] at this
      exact congrArg Subtype.val this
    intro w
    have h1 : α (z₀ ^ 3) w = w := by rw [hpow, map_one]; rfl
    rw [map_pow, pow_three] at h1
    exact h1
  have hne : ∃ w, z w ≠ w := by
    refine ⟨Additive.ofMul (QuotientGroup.mk ⟨u₀, hu₀U⟩), fun h => hcu₀ ?_⟩
    rw [hzc, hρ₁mk] at h
    have h2 := (hmk _ _).1 (Additive.ofMul.injective h)
    have h3 := hWn u₀ hu₀U _ (W.inv_mem h2)
    rw [show u₀ * ((c * u₀ * c⁻¹)⁻¹ * u₀)⁻¹ * u₀⁻¹ = c * u₀ * c⁻¹ * u₀⁻¹ by group] at h3
    exact h3
  set p : Additive (↥U ⧸ N) →ₗ[ZMod 2] Additive (↥U ⧸ N) := z ∘ₗ z + z + LinearMap.id with hp
  set W₀ := LinearMap.ker p with hW₀
  have hmemW₀ : ∀ w, w ∈ W₀ ↔ z (z w) + z w + w = 0 := fun w => Iff.rfl
  have hinv : ∀ γ, ∀ w ∈ W₀, α γ w ∈ W₀ := by
    intro γ w hw
    rw [hmemW₀] at hw ⊢
    have h := congrArg (α γ) hw
    rw [map_add, map_add, map_zero, hαz γ (z w), hαz γ w] at h
    exact h
  obtain ⟨w₁, hw₁⟩ := hne
  have hu : z w₁ + w₁ ∈ W₀ := by
    rw [hmemW₀]
    have e1 : z (z w₁ + w₁) = z (z w₁) + z w₁ := map_add z _ _
    have e2 : z (z (z w₁ + w₁)) = w₁ + z (z w₁) := by rw [e1, map_add, hz3]
    rw [e2, e1]
    have e3 : (w₁ + z (z w₁)) + (z (z w₁) + z w₁) + (z w₁ + w₁) =
        (w₁ + w₁) + (z (z w₁) + z (z w₁)) + (z w₁ + z w₁) := by abel
    rw [e3]
    simp [add_self_zmod2]
  have hu0 : z w₁ + w₁ ≠ 0 := fun h => by
    have h' : z w₁ = -w₁ := eq_neg_of_add_eq_zero_left h
    exact hw₁ (by rw [h', neg_eq_self_zmod2])
  let W' : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ U,
        Additive.ofMul (QuotientGroup.mk (⟨g, hg⟩ : ↥U) : ↥U ⧸ N) ∈ W₀}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨U.mul_mem ha hb, ?_⟩
        have e : (QuotientGroup.mk (⟨a * b, U.mul_mem ha hb⟩ : ↥U) : ↥U ⧸ N) =
            QuotientGroup.mk ⟨a, ha⟩ * QuotientGroup.mk ⟨b, hb⟩ := rfl
        rw [e, ofMul_mul]
        exact W₀.add_mem ha' hb'
      one_mem' := ⟨U.one_mem, by
        have e : (QuotientGroup.mk (⟨1, U.one_mem⟩ : ↥U) : ↥U ⧸ N) = 1 := rfl
        rw [e, ofMul_one]
        exact W₀.zero_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨U.inv_mem ha, ?_⟩
        have e : (QuotientGroup.mk (⟨a⁻¹, U.inv_mem ha⟩ : ↥U) : ↥U ⧸ N) =
            (QuotientGroup.mk ⟨a, ha⟩)⁻¹ := rfl
        rw [e, ofMul_inv]
        exact W₀.neg_mem ha' }
  have hWW' : W ≤ W' := fun w hw => ⟨hWU.le hw, by
    have e : (QuotientGroup.mk (⟨w, hWU.le hw⟩ : ↥U) : ↥U ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hw)
    rw [e, ofMul_one]
    exact W₀.zero_mem⟩
  have hW'U : W' ≤ U := fun g hg => hg.1
  have hLW' : L ≤ Subgroup.normalizer (W' : Set G) := by
    have key : ∀ l' : ↥L, ∀ g ∈ W', (l' : G) * g * (l' : G)⁻¹ ∈ W' := by
      rintro l' g ⟨hg, hg'⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hLU l'.2) g).mp hg, ?_⟩
      have := hinv (QuotientGroup.mk l') _ hg'
      rw [hαmk, hρ₁mk] at this
      exact this
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key ⟨l, hl⟩ g, fun h => ?_⟩
    have := key (⟨l, hl⟩ : ↥L)⁻¹ _ h
    rwa [show (((⟨l, hl⟩ : ↥L)⁻¹ : ↥L) : G) * (l * g * l⁻¹) * (((⟨l, hl⟩ : ↥L)⁻¹ : ↥L) : G)⁻¹ =
      g by push_cast; group] at this
  have hall : ∀ w, w ∈ W₀ := by
    intro w
    obtain ⟨m, rfl⟩ := Additive.ofMul.surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective m
    rcases hirr W' hWW' hW'U hLW' with h | h
    · exfalso
      obtain ⟨m₁, hm₁⟩ := Additive.ofMul.surjective (z w₁ + w₁)
      obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective m₁
      have hx₁ : (x₁ : G) ∈ W' := ⟨x₁.2, by rw [hm₁]; exact hu⟩
      rw [h] at hx₁
      have e : (QuotientGroup.mk x₁ : ↥U ⧸ N) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hx₁)
      apply hu0
      rw [← hm₁, e, ofMul_one]
    · have hx : (x : G) ∈ W' := by rw [h]; exact x.2
      obtain ⟨hxU, hx'⟩ := hx
      exact hx'
  have hz : ∀ w, z (z w) = z w + w := by
    intro w
    have h := (hmemW₀ w).1 (hall w)
    have h' : z (z w) = -(z w + w) := eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact h)
    rw [h', neg_eq_self_zmod2]
  have h3 := three_dvd_finrank z hz hhat.1 α hαz z₀ (fun x => rfl)
  exact ⟨_, h3, (natCard_F4Space z hz).symm.trans rfl |>.symm⟩

open Matrix Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
  {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}
  {γ : ↥(conjClosure V S.G1) →* Multiplicative (Fin 6 → ZMod 2)} {g c : G}

local notation "UL" => conjClosure (conjClosure S.V3 S.G1) L

theorem false_of_hatChief
    [IsMulCommutative ↥(conjClosure V S.G1)] (hhat : IsHatA6 L) (D : S.LineData ρ β)
    (hg : S.GData g)
    (hc : S.CData c) (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) {c₀ : G}
    (hc₀ : c₀ ∈ l0 L) (hc₀3 : c₀ ^ 3 = 1) (hc₀1 : c₀ ≠ 1) : False := by
  have hcm := S.UL_comm D hg hc hγ hΘ
  have hK : ∀ a ∈ UL, ∀ b ∈ UL, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hcm ha) b hb).symm
  have hsq := S.UL_sq D hg hc hγ hΘ
  have hLUL : L ≤ Subgroup.normalizer (UL : Set G) := le_normalizer_conjClosure _ L
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := S.frame.L_le
  have hc₀L : c₀ ∈ L := l0_le_L hc₀
  have hcV : Nat.card ↥V = 16 := S.card_V
  have hUL1 := S.card_UL_le D hg hc hγ hΘ
  have hUL2 := S.card_UL_ge D hg hc hγ hΘ
  have hVUL : V ≤ UL := (S.V_le_U0 (S.frame.L_le hg.L) hg.H).trans
    ((S.U0_le_Xs D hg.L hg.N hg.H hγ hΘ).trans (S.Xs_le_UL D hg hc hγ hΘ))
  have key : ∀ A X : Subgroup G, V ≤ A → A < X → X ≤ UL →
      L ≤ Subgroup.normalizer (A : Set G) → L ≤ Subgroup.normalizer (X : Set G) →
      (∀ W' : Subgroup G, A ≤ W' → W' ≤ X → L ≤ Subgroup.normalizer (W' : Set G) →
        W' = A ∨ W' = X) → 64 ≤ A.relIndex X ∧ (A.relIndex X ≤ 1024 → A.relIndex X = 64) := by
    intro A X hVA hAX hXU hLA hLX hirr
    have hAU : A ≤ UL := hAX.le.trans hXU
    have h := relIndex_eq_four_pow_of_hat hhat hAX
      (fun a ha b hb => by rw [hK a (hXU ha) b (hXU hb)]; simp)
      (fun a ha => by rw [hsq a (hXU ha)]; exact A.one_mem) hLX hLA
      (S.pCore_comm_mem D hg hc hγ hΘ hAX hXU hLA hLX hirr) hirr ?_
    · obtain ⟨d, ⟨k, rfl⟩, hd⟩ := h
      have hk : k ≠ 0 := by
        rintro rfl
        rw [mul_zero, pow_zero, Subgroup.relIndex_eq_one] at hd
        exact hAX.not_ge hd
      have e : (4 : ℕ) ^ (3 * k) = 64 ^ k := by rw [pow_mul]; norm_num
      rw [hd, e]
      refine ⟨Nat.le_self_pow hk 64, fun h1 => ?_⟩
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · rw [show k = 1 by omega, pow_one]
      · have h2 := (Nat.pow_le_pow_right (by norm_num : 1 ≤ 64) hk2).trans h1
        norm_num at h2
    · by_contra hcon
      push Not at hcon
      exact hAX.not_ge (S.le_of_comm_mem D hg hc hγ hΘ hc₀ hc₀3 hc₀1 hVA hXU hAU (hLA hc₀L)
        (hcon c₀ hc₀))
  have hrel : ∀ A X : Subgroup G, A ≤ X → A.relIndex X * Nat.card ↥A = Nat.card ↥X :=
    fun A X h => by rw [← Subgroup.relIndex_mul_card A X, inf_eq_left.2 h]
  have hVUL' : V < UL := lt_of_le_of_ne hVUL (fun h => by rw [← h, hcV] at hUL2; omega)
  obtain ⟨A₁, hVA₁, hA₁, hLA₁, hirr₁⟩ := exists_chief hVUL' hLV
  obtain ⟨h1, h1r⟩ := key A₁ UL hVA₁ hA₁ le_rfl hLA₁ hLUL hirr₁
  have h1' := hrel A₁ UL hA₁.le
  have hA₁V : Nat.card ↥V ≤ Nat.card ↥A₁ := Subgroup.card_le_of_le hVA₁
  have hr1 : A₁.relIndex UL = 64 := h1r (by nlinarith)
  rw [hr1] at h1'
  have hVA₁' : V < A₁ := lt_of_le_of_ne hVA₁ (fun h => by
    rw [← h, hcV] at h1'
    omega)
  obtain ⟨A₂, hVA₂, hA₂, hLA₂, hirr₂⟩ := exists_chief hVA₁' hLV
  have h2 := (key A₂ A₁ hVA₂ hA₂ hA₁.le hLA₂ hLA₁ hirr₂).1
  have h2' := hrel A₂ A₁ hA₂.le
  have hA₂V : Nat.card ↥V ≤ Nat.card ↥A₂ := Subgroup.card_le_of_le hVA₂
  nlinarith

end Setting4

theorem input13828Six_holds (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h13314 : Stmt13_3_14) : Input13828Six := by
  intro G _ _ T L V S hNS hNU hG1 hab hF hst hhat
  obtain ⟨K, ρ, β, hd⟩ := S.exists_hatData hst hhat
  obtain ⟨-, -, -, -, -, hρs, hker, -, hβk, hβe⟩ := id hd
  have hVU : V ⊓ conjClosure S.V3 S.G1 = S.V3 := S.V_inf_UH hNS h13315 h1356two hG1 h13314
  have hv0 : S.v04 ∉ conjClosure S.V3 S.G1 := fun h =>
    S.v04_not_mem_V3 (hVU ▸ Subgroup.mem_inf.2 ⟨S.v04_mem_V, h⟩)
  have hQu1 : ∃ q ∈ pCoreOf 2 S.G1, q * S.u1 * q⁻¹ ≠ S.u1 := by
    by_contra hcon
    push Not at hcon
    exact S.u1_not_mem_V1 (S.mem_V1_of_fix_QH hNS h13315 h1356two hG1 h13314 S.u1_mem_V3 hcon)
  have D : S.LineData ρ β :=
    ⟨hF, hG1, hρs, hker, hβk, hβe, hv0, hVU, hQu1, S.card_UH_hat hd⟩
  obtain ⟨x, hxX, ⟨m, hm, hxm⟩, hxC, hxN⟩ := S.exists_X2_elem h13315
  have hxL : x ∈ L := S.L2_le_L (S.X2_le_L2 hxX)
  have hxH := S.not_mem_G1_of_odd hxN hxC hm hxm
  have hg : S.GData x := ⟨hxL, hxN, hxH, ⟨m, hm, hxm⟩⟩
  obtain ⟨c, hcL1, hcρ⟩ := S.exists_L1_c012
  have hc : S.CData (c : G) :=
    ⟨S.L1_le_L hcL1, (le_sup_left.trans hF.toHypF91.L₁T_le_H) hcL1, c.2, hcρ⟩
  obtain ⟨γ, hγs, hγk, hγe, hΘ⟩ :=
    S.exists_gamma' hF hρs hβk hβe (S.line_relations D hxL hxN hxH) hv0
  obtain ⟨c₀, hc₀, hc₀3, hc₀O, -⟩ := l0_decomp hhat
  have hc₀1 : c₀ ≠ 1 := fun h => hc₀O (h ▸ (pCoreOf 2 (l0 L)).one_mem)
  exact S.false_of_hatChief hhat D hg hc ⟨hγs, hγk, hγe⟩ hΘ hc₀ hc₀3 hc₀1

end CFSG.Quasithin.H13.A6
