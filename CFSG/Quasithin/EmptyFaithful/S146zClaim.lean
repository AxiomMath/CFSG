module

public import CFSG.Quasithin.EmptyFaithful.S146zRank2

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeC

section MIdxArith

variable {G : Type} [Group G] [Finite G]

theorem mIdx_add {X Y W : Subgroup G} (hX : IsPGroup 2 X) (hYX : Y ≤ X) (hWY : W ≤ Y) :
    mIdx X W = mIdx X Y + mIdx Y W := by
  have hY : IsPGroup 2 Y := hX.to_le hYX
  have h1 := Subgroup.relIndex_mul_relIndex W Y X hWY hYX
  rw [HypF98.relIndex_eq_two_pow_mIdx hY, HypF98.relIndex_eq_two_pow_mIdx hX,
    HypF98.relIndex_eq_two_pow_mIdx hX, ← pow_add] at h1
  have := Nat.pow_right_injective (le_refl 2) h1
  omega


theorem mIdx_anti_of_le {X Y Y' : Subgroup G} (h : Y ≤ Y') : mIdx X Y' ≤ mIdx X Y := by
  unfold mIdx
  refine padicValNat_two_le_of_dvd ?_ (Subgroup.relIndex_dvd_of_le_left X h)
  exact relIndex_ne_zero_fin _ _

theorem mIdx_inf_le_mIdx {U B C : Subgroup G} (hU : IsPGroup 2 U) (hBU : B ≤ U) :
    mIdx B (C ⊓ B) ≤ mIdx U C := by
  have hB : IsPGroup 2 B := hU.to_le hBU
  have e1 := HypF98.relIndex_eq_two_pow_mIdx (Y := C ⊓ B) hB
  have e2 := HypF98.relIndex_eq_two_pow_mIdx (Y := C) hU
  rw [Subgroup.inf_relIndex_right] at e1
  have hne : C.relIndex U ≠ 0 := relIndex_ne_zero_fin _ _
  have h3 : C.relIndex B ≤ C.relIndex U := Subgroup.relIndex_le_of_le_right hBU hne
  rw [e1, e2] at h3
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3

theorem mIdx_sup_of_inf_eq {A B W : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hWA : W ≤ A) (hWB : W ≤ B) (hinf : A ⊓ B = W) (hP : IsPGroup 2 ↥(A ⊔ B)) :
    mIdx (A ⊔ B) W = mIdx A W + mIdx B W := by
  have hA : IsPGroup 2 A := hP.to_le le_sup_left
  have hB : IsPGroup 2 B := hP.to_le le_sup_right
  obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hcomm
  rw [hinf] at hc
  have e0 := Subgroup.relIndex_mul_card W (A ⊔ B)
  have e1 := Subgroup.relIndex_mul_card W A
  have e2 := Subgroup.relIndex_mul_card W B
  rw [inf_eq_left.mpr (hWA.trans le_sup_left)] at e0
  rw [inf_eq_left.mpr hWA] at e1
  rw [inf_eq_left.mpr hWB] at e2
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have key : W.relIndex (A ⊔ B) = W.relIndex A * W.relIndex B := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hWpos hWpos) ?_
    calc W.relIndex (A ⊔ B) * (Nat.card W * Nat.card W)
        = (W.relIndex (A ⊔ B) * Nat.card W) * Nat.card W := by ring
      _ = Nat.card ↥(A ⊔ B) * Nat.card W := by rw [e0]
      _ = Nat.card A * Nat.card B := hc
      _ = (W.relIndex A * Nat.card W) * (W.relIndex B * Nat.card W) := by rw [e1, e2]
      _ = W.relIndex A * W.relIndex B * (Nat.card W * Nat.card W) := by ring
  rw [HypF98.relIndex_eq_two_pow_mIdx hP, HypF98.relIndex_eq_two_pow_mIdx hA,
    HypF98.relIndex_eq_two_pow_mIdx hB, ← pow_add] at key
  exact Nat.pow_right_injective (le_refl 2) key


theorem mIdx_centralizerMod_sum_le {Z U UK Up X : Subgroup G}
    (hU : IsPGroup 2 U) (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hUKU : UK ≤ U) (hUpU : Up ≤ U) (hZK : Z ≤ UK) (hZp : Z ≤ Up) (hinf : UK ⊓ Up = Z)
    (hUN : U ≤ Subgroup.normalizer (Z : Set G))
    (hXZ : ∀ e ∈ X, ∀ z ∈ Z, e * z * e⁻¹ ∈ Z)
    (hXK : ∀ e ∈ X, ∀ y ∈ UK, e * y * e⁻¹ ∈ UK) (hXp : ∀ e ∈ X, ∀ y ∈ Up, e * y * e⁻¹ ∈ Up)
    (hXU : ∀ e ∈ X, ∀ y ∈ U, e * y * e⁻¹ ∈ U) :
    mIdx UK (centralizerMod Z UK X) + mIdx Up (centralizerMod Z Up X) ≤
      mIdx U (centralizerMod Z U X) := by
  classical
  set CK := centralizerMod Z UK X with hCK
  set Cp := centralizerMod Z Up X with hCp
  set CU := centralizerMod Z U X with hCU
  set B := UK ⊔ Up with hB
  have hBU : B ≤ U := sup_le hUKU hUpU
  have hBP : IsPGroup 2 ↥B := hU.to_le hBU
  have hCKUK : CK ≤ UK := centralizerMod_le_left _ _ _
  have hCpUp : Cp ≤ Up := centralizerMod_le_left _ _ _
  have hCKCU : CK ≤ CU := fun x hx => ⟨hUKU hx.1, hx.2.1, hx.2.2⟩
  have hCpCU : Cp ≤ CU := fun x hx => ⟨hUpU hx.1, hx.2.1, hx.2.2⟩
  have hZCK : Z ≤ CK := fun z hz => by
    refine ⟨hZK hz, hUN (hUKU (hZK hz)), fun e he => ?_⟩
    have h1 : e * z⁻¹ * e⁻¹ ∈ Z := hXZ e he z⁻¹ (Z.inv_mem hz)
    have : z * e * z⁻¹ * e⁻¹ = z * (e * z⁻¹ * e⁻¹) := by group
    rw [this]; exact Z.mul_mem hz h1
  have hZCp : Z ≤ Cp := fun z hz => by
    refine ⟨hZp hz, hUN (hUpU (hZp hz)), fun e he => ?_⟩
    have h1 : e * z⁻¹ * e⁻¹ ∈ Z := hXZ e he z⁻¹ (Z.inv_mem hz)
    have : z * e * z⁻¹ * e⁻¹ = z * (e * z⁻¹ * e⁻¹) := by group
    rw [this]; exact Z.mul_mem hz h1
  have hCKCp : CK ⊓ Cp = Z := le_antisymm
    (fun x hx => hinf ▸ ⟨hCKUK hx.1, hCpUp hx.2⟩) (le_inf hZCK hZCp)
  have hsplit : CU ⊓ B = CK ⊔ Cp := by
    apply le_antisymm
    · intro b hb
      obtain ⟨hbCU, hbB⟩ := hb
      have hNK : UK ≤ Subgroup.normalizer (Up : Set G) :=
        le_normalizer_of_forall_commute fun x hx y hy => hUc x (hUKU hx) y (hUpU hy)
      have hb' : b ∈ ((UK ⊔ Up : Subgroup G) : Set G) := hbB
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hNK] at hb'
      obtain ⟨a, ha, a', ha', rfl⟩ := Set.mem_mul.mp hb'
      have haU := hUKU ha
      have ha'U := hUpU ha'
      have hmem : ∀ e ∈ X, (e * a * e⁻¹ * a⁻¹) ∈ Z ∧ (e * a' * e⁻¹ * a'⁻¹) ∈ Z := by
        intro e he
        have h1 : a * a' * e * (a * a')⁻¹ * e⁻¹ ∈ Z := hbCU.2.2 e he
        have h2 : e * (a * a') * e⁻¹ * (a * a')⁻¹ = (e * a * e⁻¹ * a⁻¹) * (e * a' * e⁻¹ * a'⁻¹) :=
          comm_mul_of_abelian hUc (fun x hx => hXU e he x hx) haU ha'U
        have h3 : e * (a * a') * e⁻¹ * (a * a')⁻¹ ∈ Z := by
          have : e * (a * a') * e⁻¹ * (a * a')⁻¹ = (a * a' * e * (a * a')⁻¹ * e⁻¹)⁻¹ := by group
          rw [this]; exact Z.inv_mem h1
        rw [h2] at h3
        set c₁ := e * a * e⁻¹ * a⁻¹ with hc₁
        set c₂ := e * a' * e⁻¹ * a'⁻¹ with hc₂
        have hc₁K : c₁ ∈ UK := UK.mul_mem (hXK e he a ha) (UK.inv_mem ha)
        have hc₂p : c₂ ∈ Up := Up.mul_mem (hXp e he a' ha') (Up.inv_mem ha')
        have hc₁p : c₁ ∈ Up := by
          have : c₁ = (c₁ * c₂) * c₂⁻¹ := by group
          rw [this]; exact Up.mul_mem (hZp h3) (Up.inv_mem hc₂p)
        have hc₁Z : c₁ ∈ Z := hinf ▸ ⟨hc₁K, hc₁p⟩
        refine ⟨hc₁Z, ?_⟩
        have : c₂ = c₁⁻¹ * (c₁ * c₂) := by group
        rw [this]; exact Z.mul_mem (Z.inv_mem hc₁Z) h3
      have haCK : a ∈ CK := ⟨ha, hUN haU, fun e he => by
        have := (hmem e he).1
        have e1 : a * e * a⁻¹ * e⁻¹ = (e * a * e⁻¹ * a⁻¹)⁻¹ := by group
        rw [e1]; exact Z.inv_mem this⟩
      have ha'Cp : a' ∈ Cp := ⟨ha', hUN ha'U, fun e he => by
        have := (hmem e he).2
        have e1 : a' * e * a'⁻¹ * e⁻¹ = (e * a' * e⁻¹ * a'⁻¹)⁻¹ := by group
        rw [e1]; exact Z.inv_mem this⟩
      exact (CK ⊔ Cp).mul_mem (Subgroup.mem_sup_left haCK) (Subgroup.mem_sup_right ha'Cp)
    · exact le_inf (sup_le hCKCU hCpCU) (sup_le (hCKUK.trans le_sup_left) (hCpUp.trans le_sup_right))
  have hPsup : IsPGroup 2 ↥(CK ⊔ Cp) :=
    hU.to_le (sup_le (hCKUK.trans hUKU) (hCpUp.trans hUpU))
  have hP1 := mIdx_sup_of_inf_eq (A := UK) (B := Up) (W := Z)
    (fun x hx y hy => hUc x (hUKU hx) y (hUpU hy)) hZK hZp hinf hBP
  have hP2 := mIdx_sup_of_inf_eq (A := CK) (B := Cp) (W := Z)
    (fun x hx y hy => hUc x (hUKU (hCKUK hx)) y (hUpU (hCpUp hy))) hZCK hZCp hCKCp hPsup
  have hBle : CK ⊔ Cp ≤ B := sup_le (hCKUK.trans le_sup_left) (hCpUp.trans le_sup_right)
  have hm1 := mIdx_add hBP hBle (hZCK.trans le_sup_left)
  have hm2 := mIdx_add (hU.to_le hUKU) hCKUK hZCK
  have hm3 := mIdx_add (hU.to_le hUpU) hCpUp hZCp
  have hle := mIdx_inf_le_mIdx (C := CU) hU hBU
  rw [hsplit] at hle
  rw [← hB] at hP1
  omega


end MIdxArith

section ACL

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mem_inf_of_card_two {A V : Subgroup G} (hA : Nat.card A = 2) (hnV : ¬ A ≤ V)
    {x : G} (hxA : x ∈ A) (hxV : x ∈ V) : x = 1 := by
  by_contra hx1
  apply hnV
  intro a ha
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).mp hA
  have h1 : (⟨x, hxA⟩ : ↥A) = y := huniq _ (fun e => hx1 (congrArg Subtype.val e))
  by_cases ha1 : a = 1
  · rw [ha1]; exact V.one_mem
  · have h2 : (⟨a, ha⟩ : ↥A) = y := huniq _ (fun e => ha1 (congrArg Subtype.val e))
    have : a = x := congrArg Subtype.val (h2.trans h1.symm)
    rw [this]; exact hxV

theorem claim_contra {Z U UK Up X C A₁ D Dg : Subgroup G}
    (hUab : IsElemAbelian 2 U) (hXab : IsElemAbelian 2 X)
    (hUN : U ≤ Subgroup.normalizer (Z : Set G))
    (hUKU : UK ≤ U) (hUpU : Up ≤ U) (hZK : Z ≤ UK) (hZp : Z ≤ Up) (hinf : UK ⊓ Up = Z)
    (hCU : C ≤ U)
    (hdec : ∀ v ∈ U, ∃ a ∈ UK, ∃ b ∈ Up, ∃ c ∈ C, v = a * (b * c))
    (hCc : ∀ c ∈ C, ∀ e ∈ X, c * e * c⁻¹ * e⁻¹ ∈ Z)
    (hXN : X ≤ Subgroup.normalizer (Z : Set G))
    (hXK : ∀ e ∈ X, ∀ y ∈ UK, e * y * e⁻¹ ∈ UK) (hXp : ∀ e ∈ X, ∀ y ∈ Up, e * y * e⁻¹ ∈ Up)
    (hXU : ∀ e ∈ X, ∀ y ∈ U, e * y * e⁻¹ ∈ U)
    (hA₁X : A₁ ≤ X) (hA₁c : Nat.card A₁ = 2) (hD : D = centralizerMod A₁ U X)
    (hnK : ¬ A₁ ≤ UK) (hnp : ¬ A₁ ≤ Up)
    (hDgX : Dg ≤ X) (hDg : ∀ x ∈ Dg, ∀ v ∈ U, x * v * x⁻¹ * v⁻¹ ∈ Z)
    (hfaith : ∀ x ∈ X, (∀ v ∈ U, x * v * x⁻¹ * v⁻¹ ∈ Z) → x ∈ Dg)
    (hle : mIdx U D ≤ mIdx X Dg) (hlt : mIdx X Dg < mIdx U (centralizerMod Z U X))
    (hNK : ¬ X ≤ centralizerMod Z X UK →
      mIdx X (centralizerMod Z X UK) + 1 ≤ mIdx UK (centralizerMod Z UK X))
    (hNp : ¬ X ≤ centralizerMod Z X Up →
      mIdx X (centralizerMod Z X Up) + 1 ≤ mIdx Up (centralizerMod Z Up X)) : False := by
  classical
  have hUp2 : IsPGroup 2 U := isPGroup_of_isElemAbelian hUab
  have hXp2 : IsPGroup 2 X := isPGroup_of_isElemAbelian hXab
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => isElemAbelian_comm hUab hx hy
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => isElemAbelian_comm hXab hx hy
  set XK := centralizerMod Z X UK with hXK'
  set Xp := centralizerMod Z X Up with hXp'
  set CU := centralizerMod Z U X with hCU'
  have hXZ : ∀ e ∈ X, ∀ z ∈ Z, e * z * e⁻¹ ∈ Z := fun e he z hz =>
    (Subgroup.mem_normalizer_iff.mp (hXN he) z).mp hz
  have hDU : D ≤ U := hD ▸ centralizerMod_le_left _ _ _
  have hDp2 : IsPGroup 2 D := hUp2.to_le hDU
  have step1 : ∀ (V W : Subgroup G), V ≤ U → Z ≤ V → ¬ A₁ ≤ V →
      (∀ e ∈ X, ∀ y ∈ V, e * y * e⁻¹ ∈ V) →
      (∀ v ∈ U, ∃ a ∈ V, ∃ b ∈ W, ∃ c ∈ C, v = a * (b * c)) →
      W ≤ U → ∀ e ∈ centralizerMod Z X W, e ∈ Subgroup.centralizer (D : Set G) := by
    intro V W hVU hZV hnV hXV hdecV hWU e he
    obtain ⟨heX, -, heW⟩ := he
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdD : d ∈ D := hd
    rw [hD] at hdD
    obtain ⟨hdU, -, hdA⟩ := hdD
    have hA : d * e * d⁻¹ * e⁻¹ ∈ A₁ := hdA e heX
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hdecV d hdU
    have haU := hVU ha
    have hbU := hWU hb
    have hcU := hCU hc
    have hbcU : b * c ∈ U := U.mul_mem hbU hcU
    have hexp : e * (a * (b * c)) * e⁻¹ * (a * (b * c))⁻¹ =
        (e * a * e⁻¹ * a⁻¹) * ((e * b * e⁻¹ * b⁻¹) * (e * c * e⁻¹ * c⁻¹)) := by
      rw [comm_mul_of_abelian hUc (fun x hx => hXU e heX x hx) haU hbcU,
        comm_mul_of_abelian hUc (fun x hx => hXU e heX x hx) hbU hcU]
    have h1 : e * a * e⁻¹ * a⁻¹ ∈ V := V.mul_mem (hXV e heX a ha) (V.inv_mem ha)
    have h2 : e * b * e⁻¹ * b⁻¹ ∈ Z := heW b hb
    have h3 : e * c * e⁻¹ * c⁻¹ ∈ Z := by
      have := hCc c hc e heX
      have e1 : e * c * e⁻¹ * c⁻¹ = (c * e * c⁻¹ * e⁻¹)⁻¹ := by group
      rw [e1]; exact Z.inv_mem this
    have hmemV : e * (a * (b * c)) * e⁻¹ * (a * (b * c))⁻¹ ∈ V := by
      rw [hexp]; exact V.mul_mem h1 (V.mul_mem (hZV h2) (hZV h3))
    have hmemA : e * (a * (b * c)) * e⁻¹ * (a * (b * c))⁻¹ ∈ A₁ := by
      have e1 : e * (a * (b * c)) * e⁻¹ * (a * (b * c))⁻¹ =
          ((a * (b * c)) * e * (a * (b * c))⁻¹ * e⁻¹)⁻¹ := by group
      rw [e1]; exact A₁.inv_mem hA
    have h1' := eq_one_of_mem_inf_of_card_two hA₁c hnV hmemA hmemV
    have : e * (a * (b * c)) = (a * (b * c)) * e := by
      calc e * (a * (b * c)) = (e * (a * (b * c)) * e⁻¹ * (a * (b * c))⁻¹) * (a * (b * c)) * e := by
            group
        _ = (a * (b * c)) * e := by rw [h1']; group
    exact this.symm
  have hdecK' : ∀ v ∈ U, ∃ a ∈ Up, ∃ b ∈ UK, ∃ c ∈ C, v = a * (b * c) := by
    intro v hv
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hdec v hv
    refine ⟨b, hb, a, ha, c, hc, ?_⟩
    have hbU := hUpU hb
    have haU := hUKU ha
    have hcU := hCU hc
    calc a * (b * c) = a * b * c := by group
      _ = b * a * c := by rw [hUc a haU b hbU]
      _ = b * (a * c) := by group
  have hXpD : Xp ≤ X ⊓ Subgroup.centralizer (D : Set G) := fun e he =>
    ⟨he.1, step1 UK Up hUKU hZK hnK hXK hdec hUpU e he⟩
  have hXKD : XK ≤ X ⊓ Subgroup.centralizer (D : Set G) := fun e he =>
    ⟨he.1, step1 Up UK hUpU hZp hnp hXp hdecK' hUKU e he⟩
  set CX := X ⊓ Subgroup.centralizer (D : Set G) with hCX
  set CD := D ⊓ Subgroup.centralizer (X : Set G) with hCD
  have hcomm : ⁅D, X⁆ ≤ A₁ := by
    rw [Subgroup.commutator_le]
    intro d hd x hx
    have hd' : d ∈ centralizerMod A₁ U X := hD ▸ hd
    exact hd'.2.2 x hx
  have hCXc : A₁ ≤ Subgroup.centralizer (D : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' : d ∈ centralizerMod A₁ U X := hD ▸ hd
    have hdN : d ∈ Subgroup.normalizer (A₁ : Set G) := hd'.2.1
    rw [normalizer_eq_centralizer_of_card_eq_two hA₁c] at hdN
    exact (Subgroup.mem_centralizer_iff.mp hdN a ha).symm
  have hCYc : A₁ ≤ Subgroup.centralizer (X : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hXc x hx a (hA₁X ha)
  have hpair := relIndex_eq_of_commutator_le (X := D) (Y := X) (C := A₁) hXab hA₁c hcomm hCXc hCYc
  have hmDX : mIdx D CD = mIdx X CX := by
    have e1 := HypF98.relIndex_eq_two_pow_mIdx (Y := CD) hDp2
    have e2 := HypF98.relIndex_eq_two_pow_mIdx (Y := CX) hXp2
    rw [e1, e2] at hpair
    exact Nat.pow_right_injective (le_refl 2) hpair
  have hCDle : CD ≤ CU := by
    intro d hd
    refine ⟨hDU hd.1, hUN (hDU hd.1), fun e he => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hd.2 e he
    have e1 : d * e * d⁻¹ * e⁻¹ = 1 := by
      calc d * e * d⁻¹ * e⁻¹ = (e * d) * d⁻¹ * e⁻¹ := by rw [this]
        _ = 1 := by group
    rw [e1]; exact Z.one_mem
  have hf1 : mIdx U CU ≤ mIdx U D + mIdx D CD := by
    have h1 : mIdx U CU ≤ mIdx U CD := mIdx_anti_of_le (X := U) hCDle
    have h2 : mIdx U CD = mIdx U D + mIdx D CD := mIdx_add hUp2 hDU (inf_le_left : CD ≤ D)
    omega
  have hDgXK : Dg ≤ XK := fun x hx => ⟨hDgX hx, hXN (hDgX hx), fun y hy => hDg x hx y (hUKU hy)⟩
  have hDgXp : Dg ≤ Xp := fun x hx => ⟨hDgX hx, hXN (hDgX hx), fun y hy => hDg x hx y (hUpU hy)⟩
  have hXKXp : XK ⊓ Xp = Dg := by
    apply le_antisymm
    · rintro x ⟨hxK, hxp⟩
      refine hfaith x hxK.1 fun v hv => ?_
      obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hdec v hv
      have haU := hUKU ha
      have hbU := hUpU hb
      have hcU := hCU hc
      have hbcU : b * c ∈ U := U.mul_mem hbU hcU
      have hexp : x * (a * (b * c)) * x⁻¹ * (a * (b * c))⁻¹ =
          (x * a * x⁻¹ * a⁻¹) * ((x * b * x⁻¹ * b⁻¹) * (x * c * x⁻¹ * c⁻¹)) := by
        rw [comm_mul_of_abelian hUc (fun y hy => hXU x hxK.1 y hy) haU hbcU,
          comm_mul_of_abelian hUc (fun y hy => hXU x hxK.1 y hy) hbU hcU]
      rw [hexp]
      have h3 : x * c * x⁻¹ * c⁻¹ ∈ Z := by
        have := hCc c hc x hxK.1
        have e1 : x * c * x⁻¹ * c⁻¹ = (c * x * c⁻¹ * x⁻¹)⁻¹ := by group
        rw [e1]; exact Z.inv_mem this
      exact Z.mul_mem (hxK.2.2 a ha) (Z.mul_mem (hxp.2.2 b hb) h3)
    · exact le_inf hDgXK hDgXp
  have hXKX : XK ≤ X := centralizerMod_le_left _ _ _
  have hXpX : Xp ≤ X := centralizerMod_le_left _ _ _
  have hsupX : XK ⊔ Xp ≤ X := sup_le hXKX hXpX
  have hPsupX : IsPGroup 2 ↥(XK ⊔ Xp) := hXp2.to_le hsupX
  have hP2 : mIdx (XK ⊔ Xp) Dg = mIdx XK Dg + mIdx Xp Dg :=
    mIdx_sup_of_inf_eq (fun x hx y hy => hXc x (hXKX hx) y (hXpX hy)) hDgXK hDgXp hXKXp hPsupX
  have hm1 : mIdx X Dg = mIdx X (XK ⊔ Xp) + mIdx (XK ⊔ Xp) Dg :=
    mIdx_add hXp2 hsupX (hDgXK.trans le_sup_left)
  have hmXK : mIdx X Dg = mIdx X XK + mIdx XK Dg := mIdx_add hXp2 hXKX hDgXK
  have hmXp : mIdx X Dg = mIdx X Xp + mIdx Xp Dg := mIdx_add hXp2 hXpX hDgXp
  have hCXle : mIdx X CX ≤ mIdx X (XK ⊔ Xp) :=
    mIdx_anti_of_le (X := X) (sup_le hXKD hXpD)
  have hCXtop : X ≤ CX → mIdx X CX = 0 := by
    intro h
    have : CX = X := le_antisymm inf_le_left h
    rw [this]
    unfold mIdx
    rw [Subgroup.relIndex_self]
    simp
  have hnXK : ¬ X ≤ XK := by
    intro h
    have h0 := hCXtop (h.trans (hXKD.trans le_rfl))
    omega
  have hnXp : ¬ X ≤ Xp := by
    intro h
    have h0 := hCXtop (h.trans (hXpD.trans le_rfl))
    omega
  have hNK' := hNK hnXK
  have hNp' := hNp hnXp
  have hsum : mIdx UK (centralizerMod Z UK X) + mIdx Up (centralizerMod Z Up X) ≤ mIdx U CU :=
    mIdx_centralizerMod_sum_le hUp2 hUc hUKU hUpU hZK hZp hinf hUN hXZ hXK hXp hXU
  omega

end ACL

end CFSG.Quasithin.ThreeC
