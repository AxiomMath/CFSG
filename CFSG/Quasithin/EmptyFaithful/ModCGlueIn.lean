module

public import CFSG.Quasithin.EmptyFaithful.ModCAbsIn
public import CFSG.Quasithin.EmptyFaithful.ModCPhi
public import CFSG.Quasithin.EmptyFaithful.ModBR4Syl
public import CFSG.Quasithin.EmptyFaithful.S14610Perm

public section

namespace CFSG.Quasithin.ModC

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Quasithin CFSG.Quasithin.G6
  CFSG.LieType.BorelTits
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem conj_gen_mem (S : Setting146 G T M) {z l u₀ h q : G} (hzZ : z ∈ quasithinOmegaOneCenter T)
    (hz1 : z ≠ 1) (hl : l ∈ M) (hu₀ : l * z * l⁻¹ = u₀) (hh : h * u₀ * h⁻¹ = u₀)
    (hq : q ∈ VZ T M) : l⁻¹ * (h * q * h⁻¹) * l ∈ uOfL22 T M := by
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hZz : ∀ x ∈ quasithinOmegaOneCenter T, x = 1 ∨ x = z := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (S.Z_eq_of_iff hx hzZ ⟨fun h => absurd h hx1, fun h => absurd h hz1⟩)
  have hz : z = l⁻¹ * u₀ * l := by rw [← hu₀]; group
  have hh' : l⁻¹ * h * l ∈ mcOf T := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    rcases hZz x hx with rfl | rfl
    · simp
    · have e : (l⁻¹ * h * l) * x * (l⁻¹ * h * l)⁻¹ = x := by
        calc (l⁻¹ * h * l) * x * (l⁻¹ * h * l)⁻¹ = l⁻¹ * (h * (l * x * l⁻¹) * h⁻¹) * l := by group
          _ = l⁻¹ * (h * u₀ * h⁻¹) * l := by rw [hu₀]
          _ = l⁻¹ * u₀ * l := by rw [hh]
          _ = x := hz.symm
      calc x * (l⁻¹ * h * l) = ((l⁻¹ * h * l) * x * (l⁻¹ * h * l)⁻¹) * (l⁻¹ * h * l) := by rw [e]
        _ = (l⁻¹ * h * l) * x := by group
  have hq' : l⁻¹ * q * l ∈ VZ T M := by
    have := (Subgroup.mem_normalizer_iff.mp (hMV (M.inv_mem hl)) q).mp hq
    simpa using this
  have h3 := mem_conjClosure (Z := VZ T M) hh' hq'
  have e : l⁻¹ * (h * q * h⁻¹) * l = (l⁻¹ * h * l) * (l⁻¹ * q * l) * (l⁻¹ * h * l)⁻¹ := by group
  rw [e]
  exact h3

theorem xg_comm (S : Setting146 G T M) {z l u₀ t : G} (hzZ : z ∈ quasithinOmegaOneCenter T)
    (hz1 : z ≠ 1) (hl : l ∈ M) (hu₀ : l * z * l⁻¹ = u₀) (htV : ∀ q ∈ VZ T M, t * q * t⁻¹ = q)
    (ht0 : t * u₀ * t⁻¹ = u₀) (K : Subgroup G) {a x : G}
    (ha : a ∈ conjClosure (VZ T M) (K ⊓ Subgroup.centralizer ({u₀} : Set G)))
    (hx : x ∈ conjClosure (VZ T M) (K ⊓ Subgroup.centralizer ({u₀} : Set G))) :
    (t * a * t⁻¹) * x = x * (t * a * t⁻¹) := by
  let P : Subgroup G := (uOfL22 T M).comap (MulAut.conj l⁻¹).toMonoidHom
  have hP : ∀ g, g ∈ P ↔ l⁻¹ * g * l ∈ uOfL22 T M := fun g => by
    show (MulAut.conj l⁻¹) g ∈ uOfL22 T M ↔ _
    simp
  have hcen : ∀ h ∈ K ⊓ Subgroup.centralizer ({u₀} : Set G), h * u₀ * h⁻¹ = u₀ := by
    intro h hh
    have h1 := Subgroup.mem_centralizer_iff.mp hh.2 u₀ rfl
    calc h * u₀ * h⁻¹ = (u₀ * h) * h⁻¹ := by rw [h1]
      _ = u₀ := by group
  have ht0' : t⁻¹ * u₀ * t = u₀ := by
    have h := (by group : u₀ = t⁻¹ * (t * u₀ * t⁻¹) * t)
    rw [ht0] at h
    exact h.symm
  have h1 : conjClosure (VZ T M) (K ⊓ Subgroup.centralizer ({u₀} : Set G)) ≤ P := by
    refine conjClosure_le fun h hh q hq => ?_
    rw [hP]
    exact conj_gen_mem S hzZ hz1 hl hu₀ (hcen h hh) hq
  have h2 : conjClosure (VZ T M) (K ⊓ Subgroup.centralizer ({u₀} : Set G)) ≤
      P.comap (MulAut.conj t).toMonoidHom := by
    refine conjClosure_le fun h hh q hq => ?_
    show t * (h * q * h⁻¹) * t⁻¹ ∈ P
    have e : t * (h * q * h⁻¹) * t⁻¹ = (t * h * t⁻¹) * q * (t * h * t⁻¹)⁻¹ := by
      have := htV q hq
      calc t * (h * q * h⁻¹) * t⁻¹ = (t * h * t⁻¹) * (t * q * t⁻¹) * (t * h * t⁻¹)⁻¹ := by group
        _ = (t * h * t⁻¹) * q * (t * h * t⁻¹)⁻¹ := by rw [this]
    rw [e, hP]
    refine conj_gen_mem S hzZ hz1 hl hu₀ ?_ hq
    calc t * h * t⁻¹ * u₀ * (t * h * t⁻¹)⁻¹ = t * (h * (t⁻¹ * u₀ * t) * h⁻¹) * t⁻¹ := by group
      _ = t * (h * u₀ * h⁻¹) * t⁻¹ := by rw [ht0']
      _ = t * u₀ * t⁻¹ := by rw [hcen h hh]
      _ = u₀ := ht0
  have hxP : l⁻¹ * x * l ∈ uOfL22 T M := (hP x).mp (h1 hx)
  have haP : l⁻¹ * (t * a * t⁻¹) * l ∈ uOfL22 T M := (hP _).mp (h2 ha)
  have hc := congrArg Subtype.val (S.abelian.is_comm.comm ⟨_, hxP⟩ ⟨_, haP⟩)
  have hc' : (l⁻¹ * x * l) * (l⁻¹ * (t * a * t⁻¹) * l) = (l⁻¹ * (t * a * t⁻¹) * l) * (l⁻¹ * x * l) := hc
  calc (t * a * t⁻¹) * x = l * ((l⁻¹ * (t * a * t⁻¹) * l) * (l⁻¹ * x * l)) * l⁻¹ := by group
    _ = l * ((l⁻¹ * x * l) * (l⁻¹ * (t * a * t⁻¹) * l)) * l⁻¹ := by rw [hc']
    _ = x * (t * a * t⁻¹) := by group

omit [Finite G] in
theorem mem_normalizer_of_conj_le_finite {X : Subgroup G} [Finite X] {g : G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let φ : X → X := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using this)
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨g * x * g⁻¹, hx⟩
  have : g * (y : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hy
  have e : (y : G) = x := by simpa using this
  rw [← e]
  exact y.2

theorem in_contradiction {H : Subgroup G} {u : G} {I I₂ K : Subgroup G}
    (c : Facts14610 T M H u I I₂) (hK : Concl14610List T M I I₂ K) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hshort : IsShort2 K) (Φ : ↥(blockU K) ≃* ↥(coreMod 6))
    (hΦ : ∀ g : MulAut ↥(blockU K), g ∈ autOn K (blockU K) ↔
      ∃ σ ∈ alternatingGroup (Fin 6), ∀ w, Φ (g w) = coreAct 6 σ (Φ w))
    (hTu : T ⊓ I = tU T u) (hN : tZero T u = T ⊓ Subgroup.normalizer (tU T u : Set G))
    (hV3 : ¬ (pCoreOf 2 H ⊓ Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.centralizer (VZ T M : Set G))) : False := by
  classical
  have S : Setting146 G T M := c.setting
  have hVW : VZ T M ≤ blockU K := (ModB.wOf1469_eq_blockU_of_short hshort) ▸ hK.v_le_w
  have hI₂I : I₂ ≤ I := c.gen ▸ le_sup_right
  have hcommW := isMulCommutative_blockU hshort
  have hKW : K ≤ Subgroup.normalizer (blockU K : Set G) := C1.le_normalizer_blockU K
  have hIW : I ≤ Subgroup.normalizer (blockU K : Set G) := fun g hg =>
    C1.mem_normalizer_blockU (hK.normal hg)
  let β : ↥I →* MulAut ↥(blockU K) := A4.actionOn (blockU K) I hIW
  have hβ : ∀ (g : ↥I) (w : ↥(blockU K)), ((β g w : ↥(blockU K)) : G) = (g : G) * w * (g : G)⁻¹ :=
    fun g w => rfl
  let K'' : Subgroup ↥I := K.subgroupOf I
  let T'' : Subgroup ↥I := (T ⊓ I).subgroupOf I
  have hK''N : K''.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hK.le).2 hK.normal
  have hKT : K'' ⊔ T'' = ⊤ := by
    have h1 : K ⊔ (T ⊓ I) = I := hK.eq_sup.symm
    rw [← Subgroup.subgroupOf_sup hK.le inf_le_right, h1, Subgroup.subgroupOf_self]
  have hKb : autOn K (blockU K) = K''.map β := by
    ext a
    rw [A4.mem_autOn_iff hKW, Subgroup.mem_map]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨(k : G), hK.le k.2⟩, k.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hy⟩, rfl⟩
  have hΘ : ∀ σ w, Φ (liftAut Φ σ w) = coreAct 6 σ (Φ w) := liftAut_apply Φ
  have hΘinj : Function.Injective (liftAut Φ) := theta_injective (by norm_num) Φ hΘ
  have hKbΘ : K''.map β = (alternatingGroup (Fin 6)).map (liftAut Φ) := by
    rw [← hKb]
    ext g
    rw [Subgroup.mem_map]
    constructor
    · intro hg
      obtain ⟨σ, hσ, hσg⟩ := (hΦ g).mp hg
      refine ⟨σ, hσ, MulEquiv.ext fun w => Φ.injective ?_⟩
      rw [hΘ, hσg w]
    · rintro ⟨σ, hσ, rfl⟩
      exact (hΦ _).mpr ⟨σ, hσ, hΘ σ⟩
  have hcardKb : Nat.card ↥(K''.map β) = 8 * 45 := by
    rw [hKbΘ, Subgroup.card_map_of_injective hΘinj, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hT2 : IsPGroup 2 ↥T'' := hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm
  have hTi : ¬ 2 ∣ T''.index := hsyl.2.2
  have h8 := ModB.card_inf_map_ge β K'' T'' hKT hT2 hTi ⟨22, by norm_num⟩ hcardKb
  have hB2 : IsPGroup 2 ↥(T''.map β) := hT2.map β
  have hTM : T ≤ M := S.hyp1281.inM.2
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hy : ∃ y ∈ yOfL22 T M ⊓ I, Odd (orderOf y) ∧ y ∉ mcOf T := by
    by_contra hcon
    push Not at hcon
    exact S.not_lI_le_mcOf hLT ((Subgroup.closure_le _).mpr fun y hy => hcon y hy.1 hy.2)
  obtain ⟨y, hyLI, hyodd, hyG⟩ := hy
  obtain ⟨z, hzZ, hzy⟩ : ∃ z ∈ quasithinOmegaOneCenter T, ¬ (z * y = y * z) := by
    by_contra hno
    push Not at hno
    exact hyG (Subgroup.mem_centralizer_iff.mpr hno)
  have hzV : z ∈ VZ T M := le_conjClosure _ _ hzZ
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hzy (by simp)
  have hyI : y ∈ I := hyLI.2
  have hyM : y ∈ M := S.hyp1281.le hyLI.1
  have hyK : y ∈ K := by
    rw [hK.eq_residual]
    exact mem_oTwoUpper_of_odd hyI hyodd
  have hvV : y * z * y⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hMV hyM) z).mp hzV
  set z' : ↥(blockU K) := ⟨z, hVW hzV⟩ with hz'
  set v' : ↥(blockU K) := ⟨y * z * y⁻¹, hVW hvV⟩ with hv'
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hv'1 : v' ≠ 1 := by
    intro h
    apply hz1
    have h1 : y * z * y⁻¹ = 1 := congrArg Subtype.val h
    calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  have hv'z' : v' ≠ z' := by
    intro h
    apply hzy
    have h1 : y * z * y⁻¹ = z := congrArg Subtype.val h
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  let V' : Subgroup ↥(blockU K) := (VZ T M).subgroupOf (blockU K)
  have hz'V : z' ∈ V' := hzV
  have hv'V : v' ∈ V' := hvV
  have hV4 : Nat.card ↥V' = 4 := by
    have : Nat.card ↥V' = Nat.card ↥(VZ T M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv
    rw [this]
    exact S.hyp.rank_two
  have hsqW : ∀ w : ↥(blockU K), w ^ 2 = 1 := fun w => Subtype.ext (hshort.2.2.1.2 w w.2)
  have hz'sq : z' * z' = 1 := by rw [← pow_two]; exact hsqW z'
  have hV : ∀ a ∈ V', a = 1 ∨ a = z' ∨ a = v' ∨ a = z' * v' := by
    intro a ha
    have hzv : z' * v' ∈ V' := V'.mul_mem hz'V hv'V
    have hd1 : z' * v' ≠ 1 := by
      intro h
      apply hv'z'
      have : v' = z'⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact inv_eq_of_mul_eq_one_right hz'sq
    have hdz : z' * v' ≠ z' := fun h => hv'1 (mul_eq_left.mp h)
    have hdv : z' * v' ≠ v' := fun h => hz'1 (mul_eq_right.mp h)
    rcases eq_or_eq_or_eq_or_eq_of_card_four hV4 (a := (1 : ↥V')) (b := ⟨z', hz'V⟩) (c := ⟨v', hv'V⟩)
      (d := ⟨z' * v', hzv⟩) (fun he => hz'1 (congrArg Subtype.val he).symm)
      (fun he => hv'1 (congrArg Subtype.val he).symm) (fun he => hd1 (congrArg Subtype.val he).symm)
      (fun he => hv'z' (congrArg Subtype.val he).symm) (fun he => hdz (congrArg Subtype.val he).symm)
      (fun he => hdv (congrArg Subtype.val he).symm) ⟨a, ha⟩ with h | h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))
  have hBz : ∀ τ ∈ T''.map β, τ z' = z' := by
    intro τ hτ
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hτ
    have htT : (t : G) ∈ T := ((ht : (t : G) ∈ T ⊓ I)).1
    have h1 := S146T.comm_Z_T htT hzZ
    apply Subtype.ext
    rw [hβ]
    show (t : G) * z * (t : G)⁻¹ = z
    calc (t : G) * z * (t : G)⁻¹ = ((t : G) * z) * (t : G)⁻¹ := rfl
      _ = (z * (t : G)) * (t : G)⁻¹ := by rw [h1]
      _ = z := by group
  have hBV : ∀ τ ∈ T''.map β, ∀ a ∈ V', τ a ∈ V' := by
    intro τ hτ a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hτ
    have htT : (t : G) ∈ T := ((ht : (t : G) ∈ T ⊓ I)).1
    have ha' : (a : G) ∈ VZ T M := ha
    show ((β t a : ↥(blockU K)) : G) ∈ VZ T M
    rw [hβ]
    exact (Subgroup.mem_normalizer_iff.mp (hMV (hTM htT)) (a : G)).mp ha'
  have hwt : ∃ k ∈ K''.map β, k z' = v' :=
    ⟨β ⟨y, hyI⟩, Subgroup.mem_map.mpr ⟨⟨y, hyI⟩, hyK, rfl⟩, Subtype.ext rfl⟩
  obtain ⟨hdec12, hdec13, hdec23, hout⟩ :=
    abstractIn6 Φ hΘ hKbΘ hB2 h8 hz'1 hv'1 hv'z' hz'V hv'V hV hBz hBV hwt

  have hVG : ∀ a ∈ VZ T M, a = 1 ∨ a = z ∨ a = y * z * y⁻¹ ∨ a = z * (y * z * y⁻¹) := by
    intro a ha
    rcases hV ⟨a, hVW ha⟩ ha with h | h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))
  have hzvV : z * (y * z * y⁻¹) ∈ VZ T M := (VZ T M).mul_mem hzV hvV
  have hzz : z * z = 1 := by rw [← pow_two]; exact S146T.Z_sq hzZ
  have hzz' : ∀ X : G, z * (z * X) = X := fun X => by rw [← mul_assoc, hzz, one_mul]
  have hzcomm : ∀ s ∈ T, s * z * s⁻¹ = z := by
    intro s hs
    have h1 := S146T.comm_Z_T hs hzZ
    calc s * z * s⁻¹ = (s * z) * s⁻¹ := rfl
      _ = (z * s) * s⁻¹ := by rw [h1]
      _ = z := by group
  have hl3 : y⁻¹ * z * y = z * (y * z * y⁻¹) := by
    have hmem : y⁻¹ * z * y ∈ VZ T M := by
      have := (Subgroup.mem_normalizer_iff.mp (hMV (M.inv_mem hyM)) z).mp hzV
      simpa using this
    rcases hVG _ hmem with h | h | h | h
    · exfalso
      apply hz1
      calc z = y * (y⁻¹ * z * y) * y⁻¹ := by group
        _ = 1 := by rw [h]; group
    · exfalso
      apply hzy
      calc z * y = y * (y⁻¹ * z * y) := by group
        _ = y * z := by rw [h]
    · exfalso
      apply hzy
      obtain ⟨m, hm⟩ := hyodd
      have hc : (y * y) * z = z * (y * y) := by
        calc (y * y) * z = y * (y * z * y⁻¹) * y := by group
          _ = y * (y⁻¹ * z * y) * y := by rw [← h]
          _ = z * (y * y) := by group
      have hcp : ∀ k : ℕ, (y * y) ^ k * z = z * (y * y) ^ k := fun k =>
        ((Commute.pow_left (show Commute (y * y) z from hc) k) : Commute ((y * y) ^ k) z)
      have hyy : (y * y) ^ (m + 1) = y := by
        rw [← pow_two, ← pow_mul]
        have : 2 * (m + 1) = orderOf y + 1 := by omega
        rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
      have := hcp (m + 1)
      rw [hyy] at this
      exact this.symm
    · exact h
  have hswap : ∀ s ∈ T, s * (y * z * y⁻¹) * s⁻¹ ≠ y * z * y⁻¹ →
      s * (y * z * y⁻¹) * s⁻¹ = z * (y * z * y⁻¹) := by
    intro s hs hne
    have hmem : s * (y * z * y⁻¹) * s⁻¹ ∈ VZ T M :=
      (Subgroup.mem_normalizer_iff.mp (hMV (hTM hs)) _).mp hvV
    rcases hVG _ hmem with h | h | h | h
    · exfalso
      apply hv'1
      refine Subtype.ext ?_
      calc y * z * y⁻¹ = s⁻¹ * (s * (y * z * y⁻¹) * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group
    · exfalso
      apply hv'z'
      refine Subtype.ext ?_
      have hsz : s⁻¹ * z * s = z := by
        have h0 : z = s⁻¹ * (s * z * s⁻¹) * s := by group
        rw [hzcomm s hs] at h0
        exact h0.symm
      calc y * z * y⁻¹ = s⁻¹ * (s * (y * z * y⁻¹) * s⁻¹) * s := by group
        _ = s⁻¹ * z * s := by rw [h]
        _ = z := hsz
    · exact absurd h hne
    · exact h
  obtain ⟨q, hq, hqV⟩ := IsConcreteLE.not_le_iff_exists.mp hV3
  have hqT : q ∈ T := S.pCoreOf_le_T c.hH hq.1
  have hqu : q ∈ tU T u := ⟨hqT, hq.2⟩
  have hqv : q * (y * z * y⁻¹) * q⁻¹ ≠ y * z * y⁻¹ := by
    intro h
    apply hqV
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have hcq : q * a * q⁻¹ = a := by
      rcases hVG a ha with h' | h' | h' | h' <;> rw [h']
      · simp
      · exact hzcomm q hqT
      · exact h
      · calc q * (z * (y * z * y⁻¹)) * q⁻¹ = (q * z * q⁻¹) * (q * (y * z * y⁻¹) * q⁻¹) := by group
          _ = z * (y * z * y⁻¹) := by rw [hzcomm q hqT, h]
    calc a * q = (q * a * q⁻¹) * q := by rw [hcq]
      _ = q * a := by group
  obtain ⟨t₀, ht₀T0, ht₀n, ht₀⟩ :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp (S.relIndex_tU_tZero c.hH c.hu)
  have ht₀T : t₀ ∈ T := S146T.tZero_le T u ht₀T0
  obtain ⟨t, htT0, htn, htv⟩ : ∃ t ∈ tZero T u, t ∉ tU T u ∧
      t * (y * z * y⁻¹) * t⁻¹ = y * z * y⁻¹ := by
    by_cases h : t₀ * (y * z * y⁻¹) * t₀⁻¹ = y * z * y⁻¹
    · exact ⟨t₀, ht₀T0, ht₀n, h⟩
    · refine ⟨t₀ * q⁻¹, (tZero T u).mul_mem ht₀T0 ((tZero T u).inv_mem (tU_le_tZero T u hqu)), ?_, ?_⟩
      · intro hmem
        apply ht₀n
        have := (tU T u).mul_mem hmem hqu
        simpa using this
      · have h1 := hswap q hqT hqv
        have h2 := hswap t₀ ht₀T h
        have hqz : q⁻¹ * z * q = z := by
          have h0 : z = q⁻¹ * (q * z * q⁻¹) * q := by group
          rw [hzcomm q hqT] at h0
          exact h0.symm
        have e : y * z * y⁻¹ = z * (q⁻¹ * (y * z * y⁻¹) * q) := by
          calc y * z * y⁻¹ = q⁻¹ * (q * (y * z * y⁻¹) * q⁻¹) * q := by group
            _ = q⁻¹ * (z * (y * z * y⁻¹)) * q := by rw [h1]
            _ = (q⁻¹ * z * q) * (q⁻¹ * (y * z * y⁻¹) * q) := by group
            _ = z * (q⁻¹ * (y * z * y⁻¹) * q) := by rw [hqz]
        have h3 : q⁻¹ * (y * z * y⁻¹) * q = z * (y * z * y⁻¹) := by
          calc q⁻¹ * (y * z * y⁻¹) * q = z * (z * (q⁻¹ * (y * z * y⁻¹) * q)) := (hzz' _).symm
            _ = z * (y * z * y⁻¹) := by rw [← e]
        calc t₀ * q⁻¹ * (y * z * y⁻¹) * (t₀ * q⁻¹)⁻¹
            = t₀ * (q⁻¹ * (y * z * y⁻¹) * q) * t₀⁻¹ := by group
          _ = t₀ * (z * (y * z * y⁻¹)) * t₀⁻¹ := by rw [h3]
          _ = (t₀ * z * t₀⁻¹) * (t₀ * (y * z * y⁻¹) * t₀⁻¹) := by group
          _ = z * (z * (y * z * y⁻¹)) := by rw [hzcomm t₀ ht₀T, h2]
          _ = y * z * y⁻¹ := hzz' _
  have htT : t ∈ T := S146T.tZero_le T u htT0
  have htN : t ∈ Subgroup.normalizer (tU T u : Set G) := by
    have := htT0
    rw [hN] at this
    exact this.2
  have htV : ∀ a ∈ VZ T M, t * a * t⁻¹ = a := by
    intro a ha
    rcases hVG a ha with h | h | h | h <;> rw [h]
    · simp
    · exact hzcomm t htT
    · exact htv
    · calc t * (z * (y * z * y⁻¹)) * t⁻¹ = (t * z * t⁻¹) * (t * (y * z * y⁻¹) * t⁻¹) := by group
        _ = z * (y * z * y⁻¹) := by rw [hzcomm t htT, htv]
  have ht2 : t * t ∈ tU T u := by
    have hA : t * t₀ ∈ tU T u := by
      rcases ht₀ t htT0 with h | h
      · exact h
      · exact absurd h htn
    have htt : t * t ∈ tZero T u := (tZero T u).mul_mem htT0 htT0
    rcases ht₀ (t * t) htt with h | h
    · exfalso
      apply htn
      have h' := (tU T u).mul_mem h ((tU T u).inv_mem hA)
      have e : t * t * t₀ * (t * t₀)⁻¹ = t := by group
      rwa [e] at h'
    · exact h
  have hWT : blockU K ≤ T :=
    (ModB.wOf1469_eq_blockU_of_short hshort) ▸ wOf1469_le_T hK.le hK.normal hsyl
  have hWI : blockU K ≤ I := fun w hw => hK.le ((pCoreOf_le 2 K) (C1.blockU_le_blockQ hshort hw))
  have hTuI : tU T u ≤ I := by rw [← hTu]; exact inf_le_right
  have hTuT : tU T u ≤ T := by rw [← hTu]; exact inf_le_left
  have hWtU : blockU K ≤ tU T u := by rw [← hTu]; exact le_inf hWT hWI
  let B : Subgroup G := (blockU K).map (MulAut.conj t).toMonoidHom
  have hBtU : B ≤ tU T u := by
    intro b hb
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hb
    exact (Subgroup.mem_normalizer_iff.mp htN w).mp (hWtU hw)
  have hBI : ∀ b ∈ B, b ∈ I := fun b hb => hTuI (hBtU hb)
  have hmemI : ∀ w₀ : ↥(blockU K), t * (w₀ : G) * t⁻¹ ∈ I := fun w₀ =>
    hBI _ (Subgroup.mem_map.mpr ⟨w₀, w₀.2, rfl⟩)
  have hXle : ∀ u' : ↥(blockU K), Xgen (K''.map β) V' u' ≤
      (conjClosure (VZ T M) (K ⊓ Subgroup.centralizer ({(u' : G)} : Set G))).subgroupOf (blockU K) := by
    intro u'
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨σ, hσ, hσu, q, hq, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hσ
    show ((β k q : ↥(blockU K)) : G) ∈
      conjClosure (VZ T M) (K ⊓ Subgroup.centralizer ({(u' : G)} : Set G))
    rw [hβ]
    have hkK : (k : G) ∈ K := hk
    have hku : (k : G) * u' * (k : G)⁻¹ = u' := by
      have := congrArg Subtype.val hσu
      rw [hβ] at this
      exact this
    have hkC : (k : G) ∈ Subgroup.centralizer ({(u' : G)} : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff.mp hh]
      calc (u' : G) * k = ((k : G) * u' * (k : G)⁻¹) * k := by rw [hku]
        _ = k * u' := by group
    exact mem_conjClosure ⟨hkK, hkC⟩ (show (q : G) ∈ VZ T M from hq)
  have hbeta_cen : ∀ (u' : ↥(blockU K)) (l : G), (u' : G) ∈ VZ T M → l ∈ M →
      l * z * l⁻¹ = (u' : G) → ∀ a : ↥(blockU K), a ∈ Xgen (K''.map β) V' u' →
        β ⟨t * (a : G) * t⁻¹, hmemI a⟩ ∈ CenN (K''.map β) (Xgen (K''.map β) V' u') := by
    intro u' l hu' hl hlu a ha
    refine ⟨?_, ?_⟩
    · intro k hk
      obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk
      refine ⟨Subgroup.mem_map.mpr ⟨_, hK''N.conj_mem k₀ hk₀ ⟨t * (a : G) * t⁻¹, hmemI a⟩, ?_⟩,
        Subgroup.mem_map.mpr ⟨_, hK''N.conj_mem k₀ hk₀ ⟨t * (a : G) * t⁻¹, hmemI a⟩⁻¹, ?_⟩⟩
      · simp only [map_mul, map_inv]
      · simp only [map_mul, map_inv, inv_inv]
    · intro x hx
      apply Subtype.ext
      rw [hβ]
      have hxXg : (x : G) ∈ conjClosure (VZ T M)
          (K ⊓ Subgroup.centralizer ({(u' : G)} : Set G)) := hXle u' hx
      have haXg : (a : G) ∈ conjClosure (VZ T M)
          (K ⊓ Subgroup.centralizer ({(u' : G)} : Set G)) := hXle u' ha
      have hcm := xg_comm S hzZ hz1 hl hlu htV (htV _ hu') K haXg hxXg
      show (t * (a : G) * t⁻¹) * x * (t * (a : G) * t⁻¹)⁻¹ = x
      calc (t * (a : G) * t⁻¹) * x * (t * (a : G) * t⁻¹)⁻¹
          = ((t * (a : G) * t⁻¹) * x) * (t * (a : G) * t⁻¹)⁻¹ := rfl
        _ = (x * (t * (a : G) * t⁻¹)) * (t * (a : G) * t⁻¹)⁻¹ := by rw [hcm]
        _ = x := by group
  have hkey : ∀ (u u' : ↥(blockU K)) (l l' : G), (u : G) ∈ VZ T M → (u' : G) ∈ VZ T M →
      l ∈ M → l' ∈ M → l * z * l⁻¹ = (u : G) → l' * z * l'⁻¹ = (u' : G) →
      Xgen (K''.map β) V' u ⊔ Xgen (K''.map β) V' u' = ⊤ → ∀ w₀ : ↥(blockU K),
        ∃ p₁ ∈ CenN (K''.map β) (Xgen (K''.map β) V' u),
          ∃ p₂ ∈ CenN (K''.map β) (Xgen (K''.map β) V' u'),
            β ⟨t * (w₀ : G) * t⁻¹, hmemI w₀⟩ = p₁ * p₂ := by
    intro u u' l l' hu hu' hl hl' hlu hlu' hdec w₀
    have hw₀ : w₀ ∈ Xgen (K''.map β) V' u ⊔ Xgen (K''.map β) V' u' := by
      rw [hdec]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, c, hc, hac⟩ := Subgroup.mem_sup.mp hw₀
    refine ⟨_, hbeta_cen u l hu hl hlu a ha, _, hbeta_cen u' l' hu' hl' hlu' c hc, ?_⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show t * (w₀ : G) * t⁻¹ = (t * (a : G) * t⁻¹) * (t * (c : G) * t⁻¹)
    rw [← hac]
    simp only [Subgroup.coe_mul]
    group
  have hvVz : ((v' : ↥(blockU K)) : G) ∈ VZ T M := hvV
  have hzvV' : (((z' * v' : ↥(blockU K))) : G) ∈ VZ T M := hzvV
  have hBW : ∀ b ∈ B, ∀ w ∈ blockU K, b * w * b⁻¹ = w := by
    intro b hb w hw
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨p₁, hp₁, p₂, hp₂, e12⟩ := hkey z' v' 1 y hzV hvV M.one_mem hyM (by simp [hz'])
      (by simp [hv']) hdec12 ⟨w₀, hw₀⟩
    obtain ⟨p₁', hp₁', p₃, hp₃, e13⟩ := hkey z' (z' * v') 1 y⁻¹ hzV hzvV M.one_mem (M.inv_mem hyM)
      (by simp [hz']) (by simpa [hz', hv'] using hl3) hdec13 ⟨w₀, hw₀⟩
    obtain ⟨p₂', hp₂', p₃', hp₃', e23⟩ := hkey v' (z' * v') y y⁻¹ hvV hzvV hyM (M.inv_mem hyM)
      (by simp [hv']) (by simpa [hz', hv'] using hl3) hdec23 ⟨w₀, hw₀⟩
    have h1 := hout _ ⟨p₁, hp₁, p₂, hp₂, e12⟩ ⟨p₁', hp₁', p₃, hp₃, e13⟩ ⟨p₂', hp₂', p₃', hp₃', e23⟩
    have h2 : β ⟨t * w₀ * t⁻¹, hmemI ⟨w₀, hw₀⟩⟩ ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [h1]; rfl
    have h3 := congrArg Subtype.val h2
    rw [hβ] at h3
    exact h3
  have hCnorm : ∀ g ∈ Subgroup.normalizer (blockU K : Set G),
      ∀ x ∈ Subgroup.centralizer (blockU K : Set G),
        g * x * g⁻¹ ∈ Subgroup.centralizer (blockU K : Set G) := by
    intro g hg x hx
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have hw' : g⁻¹ * w * g ∈ blockU K := by
      refine (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * w * g)).mpr ?_
      have e : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
      rw [e]
      exact hw
    have h1 := Subgroup.mem_centralizer_iff.mp hx _ hw'
    calc w * (g * x * g⁻¹) = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * w := by group
  have hbK : ∀ b ∈ B, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ blockU K := by
    intro b hb
    have hbI : b ∈ I := hBI b hb
    have hbC : b ∈ Subgroup.centralizer (blockU K : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun w hw => by
        have := hBW b hb w hw
        calc w * b = (b * w * b⁻¹) * b := by rw [this]
          _ = b * w := by group
    refine C1.commutator_mem_blockU_of_mem_blockQ hshort (y := b) (fun k hk => ?_)
    have hbkK : b * k * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hK.normal hbI) k).mp hk
    have hc1 : b * k * b⁻¹ * k⁻¹ ∈ K := K.mul_mem hbkK (K.inv_mem hk)
    have hc2 : b * k * b⁻¹ * k⁻¹ ∈ Subgroup.centralizer (blockU K : Set G) := by
      have h1 := hCnorm k (hKW hk) b⁻¹ ((Subgroup.centralizer (blockU K : Set G)).inv_mem hbC)
      have := (Subgroup.centralizer (blockU K : Set G)).mul_mem hbC h1
      simpa [mul_assoc] using this
    exact C1.inf_centralizer_blockU_le hshort ⟨hc1, hc2⟩
  let WB : Subgroup G := blockU K ⊔ B
  have hBconj : ∀ s ∈ tU T u, ∀ b ∈ B, s * b * s⁻¹ ∈ B := by
    intro s hs b hb
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hb
    have hs' : t⁻¹ * s * t ∈ tU T u := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem htN) s).mp hs
      simpa using this
    have hw' : (t⁻¹ * s * t) * w * (t⁻¹ * s * t)⁻¹ ∈ blockU K :=
      (Subgroup.mem_normalizer_iff.mp (hIW (hTuI hs')) w).mp hw
    refine Subgroup.mem_map.mpr ⟨_, hw', ?_⟩
    show t * ((t⁻¹ * s * t) * w * (t⁻¹ * s * t)⁻¹) * t⁻¹ = s * (t * w * t⁻¹) * s⁻¹
    group
  have hKWB : ∀ k ∈ K, WB ≤ WB.comap (MulAut.conj k).toMonoidHom := by
    intro k hk
    refine sup_le (fun w hw => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hKW hk) w).mp hw)
    · show k * b * k⁻¹ ∈ WB
      have h := hbK b hb k hk
      have e : k * b * k⁻¹ = (b * k * b⁻¹ * k⁻¹)⁻¹ * b := by group
      rw [e]
      exact Subgroup.mul_mem_sup ((blockU K).inv_mem h) hb
  have hTWB : ∀ s ∈ tU T u, WB ≤ WB.comap (MulAut.conj s).toMonoidHom := by
    intro s hs
    refine sup_le (fun w hw => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hIW (hTuI hs)) w).mp hw)
    · exact Subgroup.mem_sup_right (hBconj s hs b hb)
  have htWB : WB ≤ WB.comap (MulAut.conj t).toMonoidHom := by
    refine sup_le (fun w hw => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
    · obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hb
      show t * (t * w * t⁻¹) * t⁻¹ ∈ WB
      have e : t * (t * w * t⁻¹) * t⁻¹ = (t * t) * w * (t * t)⁻¹ := by group
      rw [e]
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hIW (hTuI ht2)) w).mp hw)
  have hKN : K ≤ Subgroup.normalizer (WB : Set G) := fun k hk =>
    mem_normalizer_of_conj_le_finite fun x hx => hKWB k hk hx
  have hTuN : tU T u ≤ Subgroup.normalizer (WB : Set G) := fun s hs =>
    mem_normalizer_of_conj_le_finite fun x hx => hTWB s hs hx
  have htNWB : t ∈ Subgroup.normalizer (WB : Set G) :=
    mem_normalizer_of_conj_le_finite fun x hx => htWB hx
  have hIN : I ≤ Subgroup.normalizer (WB : Set G) := by
    rw [hK.eq_sup]
    exact sup_le hKN (hTu ▸ hTuN)
  let J : Subgroup G := I ⊔ Subgroup.zpowers t
  have hJN : J ≤ Subgroup.normalizer (WB : Set G) := sup_le hIN (Subgroup.zpowers_le.mpr htNWB)
  have hWBI : WB ≤ I := sup_le hWI (fun b hb => hBI b hb)
  have hWBJ : WB ≤ J := hWBI.trans le_sup_left
  have hWB2 : IsPGroup 2 WB := S.hyp.sylow.1.to_le (sup_le hWT (hBtU.trans hTuT))
  have hWBle : WB ≤ pCoreOf 2 J := le_pCoreOf_of_le_normalizer 2 hWBJ hJN hWB2
  have hJ0 : pCoreOf 2 J ≠ ⊥ := by
    intro hbot
    have h1 : z ∈ pCoreOf 2 J := hWBle (Subgroup.mem_sup_left (hVW hzV))
    rw [hbot] at h1
    exact hz1 (Subgroup.mem_bot.mp h1)
  have hJst := IsIStar.of_le c.hI (le_sup_left : I ≤ J) hJ0
  have htJ : t ∈ T ⊓ J := ⟨htT, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩
  rw [hJst.2, hTu] at htJ
  exact htn htJ

end CFSG.Quasithin.ModC
