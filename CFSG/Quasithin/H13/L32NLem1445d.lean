module

public import CFSG.Quasithin.H13.L32NLem1445c
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.Quasithin.H13.L32NLem1444o
public import CFSG.Quasithin.H13.L32NSymA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace L1444

variable {G : Type} [Group G] [Finite G]

namespace Setup5

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup5 G T L V V₂ g D Q₁ Q₂)
include S

theorem V_le_cent : V ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := fun _ hv =>
  ⟨Subgroup.mem_sup_left (S.V_le_L hv),
    Subgroup.mem_centralizer_iff.mpr fun _ hw => S.comm_V hw hv⟩

theorem normalizer_cent_le
    (huniq : ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → L ⊔ T ≤ M →
      M = Subgroup.normalizer (L : Set G))
    (hNL : Subgroup.normalizer (L : Set G) = L ⊔ T) :
    Subgroup.normalizer (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ≤
      L ⊔ T := by
  have hne : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≠ ⊥ := by
    intro h
    have hVC := S.V_le_cent
    rw [h] at hVC
    have := Subgroup.card_le_of_le hVC
    rw [S.card8, Subgroup.card_bot] at this
    omega
  obtain ⟨M, hM, hle⟩ := exists_maxTwoLocal_ge (⟨_, hne, S.isPGroup_cent, rfl⟩ : IsTwoLocal _)
  have hMeq := huniq M hM (S.le_normalizer_cent.trans hle)
  rw [hMeq, hNL] at hle
  exact hle

theorem isSylowTwoOf_cent (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (huniq : ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → L ⊔ T ≤ M →
      M = Subgroup.normalizer (L : Set G))
    (hNL : Subgroup.normalizer (L : Set G) = L ⊔ T) {s : G}
    (hs : s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hsV : s ∉ V)
    (h168 : Nat.card ↥(L ⊓ Subgroup.centralizer ({s} : Set G)) = 168) :
    IsSylowTwoOf ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))
      (Subgroup.centralizer ({s} : Set G)) := by
  refine L1445.isSylowTwoOf_of_normalizer (fun c hc => ?_) S.isPGroup_cent
    fun P hCP hPZ hPN hP2 => ?_
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (S.comm_cent hCTL hc hs)
  · exact S.le_cent_of_isPGroup hCTL hs hsV h168 hCP
      (le_inf (hPN.trans (S.normalizer_cent_le huniq hNL)) hPZ) hP2

omit S in
theorem elem_of_le_cent {C : Subgroup G} {s : G}
    (hSyl : IsSylowTwoOf C (Subgroup.centralizer ({s} : Set G)))
    (hCc : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) (hC2 : ∀ a ∈ C, a * a = 1) {P : Subgroup G}
    (hP : P ≤ Subgroup.centralizer ({s} : Set G)) (hP2 : IsPGroup 2 P) :
    (∀ a ∈ P, ∀ b ∈ P, a * b = b * a) ∧ ∀ a ∈ P, a * a = 1 := by
  obtain ⟨Q, hPQ, hQ⟩ := exists_isSylowTwoOf_of_le hP hP2
  obtain ⟨h, -, hQeq⟩ := hSyl.exists_conj hQ
  have hmem : ∀ a ∈ P, ∃ c ∈ C, h * c * h⁻¹ = a := by
    intro a ha
    have : a ∈ C.map (MulAut.conj h).toMonoidHom := hQeq ▸ hPQ ha
    obtain ⟨c, hc, rfl⟩ := this
    exact ⟨c, hc, rfl⟩
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := hmem a ha
    obtain ⟨c', hc', rfl⟩ := hmem b hb
    calc h * c * h⁻¹ * (h * c' * h⁻¹) = h * (c * c') * h⁻¹ := by group
      _ = h * (c' * c) * h⁻¹ := by rw [hCc c hc c' hc']
      _ = h * c' * h⁻¹ * (h * c * h⁻¹) := by group
  · obtain ⟨c, hc, rfl⟩ := hmem a ha
    calc h * c * h⁻¹ * (h * c * h⁻¹) = h * (c * c) * h⁻¹ := by group
      _ = 1 := by rw [hC2 c hc]; group

theorem exists_conj_mem_U {b : G} (hb : b ∈ L) (hb2 : b * b = 1) :
    ∃ l ∈ L, l * b * l⁻¹ ∈ fsuU T V := by
  obtain ⟨_, S'⟩ := S.set14
  by_cases hbV : b ∈ V
  · exact ⟨1, L.one_mem, by simpa using V_le_U hbV⟩
  have hbN := S.L_le_normV hb
  have hconj : ∀ v ∈ V, b * v * b⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hbN v).mp hv
  have hmemφ : ∀ v : V, b * (v : G) * b⁻¹ * (v : G)⁻¹ ∈ V := fun v =>
    V.mul_mem (hconj _ v.2) (V.inv_mem v.2)
  let φ : V →* V :=
    { toFun := fun v => ⟨b * v * b⁻¹ * (v : G)⁻¹, hmemφ v⟩
      map_one' := by ext; simp
      map_mul' := fun v w => by
        apply Subtype.ext
        show b * ((v : G) * w) * b⁻¹ * ((v : G) * w)⁻¹ =
          b * v * b⁻¹ * (v : G)⁻¹ * (b * w * b⁻¹ * (w : G)⁻¹)
        have h1 := S.comm_V (hmemφ w) (V.inv_mem v.2)
        calc b * ((v : G) * w) * b⁻¹ * ((v : G) * w)⁻¹
            = b * v * b⁻¹ * ((b * w * b⁻¹ * (w : G)⁻¹) * (v : G)⁻¹) := by group
          _ = b * v * b⁻¹ * ((v : G)⁻¹ * (b * w * b⁻¹ * (w : G)⁻¹)) := by rw [h1]
          _ = b * v * b⁻¹ * (v : G)⁻¹ * (b * w * b⁻¹ * (w : G)⁻¹) := by group }
  have hφ : ∀ v : V, ((φ v : V) : G) = b * v * b⁻¹ * (v : G)⁻¹ := fun v => rfl
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2
  have hφφ : ∀ v : V, φ (φ v) = 1 := by
    intro v
    apply Subtype.ext
    show b * ((φ v : V) : G) * b⁻¹ * ((φ v : V) : G)⁻¹ = 1
    rw [hφ]
    set x := b * (v : G) * b⁻¹ * (v : G)⁻¹ with hx
    have hxx : x * x = 1 := by rw [← pow_two]; exact S.elem.2 x (hmemφ v)
    have e1 : b * x * b⁻¹ = (b * b) * ((v : G) * b⁻¹ * (v : G)⁻¹ * b⁻¹) := by rw [hx]; group
    have e2 : x⁻¹ = (v : G) * b * (v : G)⁻¹ * b⁻¹ := by rw [hx]; group
    have hbx : b * x * b⁻¹ = x⁻¹ := by
      rw [e1, e2, hb2, one_mul, hbinv]
    rw [hbx, ← mul_inv_rev, hxx, inv_one]
  have hrk : φ.range ≤ φ.ker := by
    rintro _ ⟨v, rfl⟩
    exact MonoidHom.mem_ker.mpr (hφφ v)
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, φ v₀ ≠ 1 := by
    by_contra h
    push Not at h
    apply hbV
    refine S.centL.le ⟨hb, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h1 : b * v * b⁻¹ * v⁻¹ = 1 := by
      have := congrArg Subtype.val (h ⟨v, hv⟩)
      rw [hφ] at this
      exact this
    calc v * b = (b * v * b⁻¹ * v⁻¹)⁻¹ * (b * v) := by group
      _ = b * v := by rw [h1, inv_one, one_mul]
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [S.card8] at hcard
  have hr2 : 2 ≤ Nat.card φ.range := by
    have hne : φ.range ≠ ⊥ := fun h => hv₀ (by
      have : φ v₀ ∈ φ.range := ⟨v₀, rfl⟩
      rw [h] at this
      exact Subgroup.mem_bot.mp this)
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have h8 : Nat.card φ.range * Nat.card φ.range ≤ 8 := by
    rw [← hcard]
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hrk)
  have hr : Nat.card φ.range = 2 := by
    have : Nat.card φ.range ≤ 2 := by
      by_contra h
      push Not at h
      have := Nat.mul_le_mul h h
      omega
    omega
  have huniq2 : ∀ v : V, φ v = 1 ∨ φ v = φ v₀ := by
    intro v
    by_cases h1 : φ v = 1
    · exact Or.inl h1
    right
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : φ.range)).mp hr
    have e1 := hy ⟨φ v, v, rfl⟩ (fun h => h1 (congrArg Subtype.val h))
    have e2 := hy ⟨φ v₀, v₀, rfl⟩ (fun h => hv₀ (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  obtain ⟨z, -, -, hz, hz1, -, -, -, -⟩ := S'.exists_basis
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hw1 : ((φ v₀ : V) : G) ≠ 1 := fun h => hv₀ (Subtype.ext h)
  obtain ⟨l, hl, hlw⟩ := L32NSym.exists_conj_eq (fun u hu => S.elem.2 u hu)
    (autOn_eq_top_of_hyp1281One S'.h1281) (φ v₀).2 hzV hw1 hz1
  refine ⟨l, hl, S.mem_U_of_comm (L.mul_mem (L.mul_mem hl hb) (L.inv_mem hl)) fun v hv => ?_⟩
  have hv' : l⁻¹ * v * l ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer _).inv_mem (S.L_le_normV hl)) v).mp hv
    simpa using this
  have e : l * b * l⁻¹ * v * (l * b * l⁻¹)⁻¹ * v⁻¹ =
      l * ((φ ⟨_, hv'⟩ : V) : G) * l⁻¹ := by
    rw [hφ]
    group
  rw [e]
  rcases huniq2 ⟨_, hv'⟩ with h | h
  · rw [h]
    simp
  · rw [h, hlw]
    exact hz

theorem card_cent_U {b : G} (hb : b ∈ fsuU T V) :
    16 ≤ Nat.card ↥(fsuU T V ⊓ Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨ψ, hψ⟩ := S.exists_hom_comm hb
  have hcardQ : Nat.card ↥(pCoreOf 2 (l32nH T V)) = 32 := by rw [← S.QU, S.card32]; norm_num
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by rw [S.zU, S.card2]
  have h1 := Subgroup.card_ker_mul_card_range ψ
  rw [hcardQ] at h1
  have hr : Nat.card ψ.range ≤ 2 := by
    have := Subgroup.card_le_card_group ψ.range
    rwa [hZ2] at this
  have hk : 16 ≤ Nat.card ψ.ker := by
    by_contra h
    push Not at h
    have := Nat.mul_le_mul (Nat.le_of_lt_succ h) hr
    omega
  refine hk.trans (Nat.card_le_card_of_injective
    (fun q => ⟨((q : ↥(pCoreOf 2 (l32nH T V))) : G), S.QU.ge (q : ↥(pCoreOf 2 (l32nH T V))).2,
      ?_⟩) ?_)
  · show ((q : ↥(pCoreOf 2 (l32nH T V))) : G) ∈ Subgroup.centralizer ({b} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hq : ψ (q : ↥(pCoreOf 2 (l32nH T V))) = 1 := MonoidHom.mem_ker.mp q.2
    have h := hψ (q : ↥(pCoreOf 2 (l32nH T V)))
    rw [hq] at h
    have h' : ((q : ↥(pCoreOf 2 (l32nH T V))) : G) * b *
        ((q : ↥(pCoreOf 2 (l32nH T V))) : G)⁻¹ * b⁻¹ = 1 := h.symm
    calc ((q : ↥(pCoreOf 2 (l32nH T V))) : G) * b
        = ((q : ↥(pCoreOf 2 (l32nH T V))) : G) * b * ((q : ↥(pCoreOf 2 (l32nH T V))) : G)⁻¹ *
            b⁻¹ * (b * q) := by group
      _ = b * q := by rw [h', one_mul]
  · intro x y hxy
    have h : ((x : ↥(pCoreOf 2 (l32nH T V))) : G) = ((y : ↥(pCoreOf 2 (l32nH T V))) : G) :=
      congrArg (fun w : ↥(fsuU T V ⊓ Subgroup.centralizer ({b} : Set G)) => (w : G)) hxy
    exact Subtype.ext (Subtype.ext h)

theorem not_conj_mem (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (huniq : ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → L ⊔ T ≤ M →
      M = Subgroup.normalizer (L : Set G))
    (hNL : Subgroup.normalizer (L : Set G) = L ⊔ T) {s : G}
    (hs : s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hsV : s ∉ V)
    (h168 : Nat.card ↥(L ⊓ Subgroup.centralizer ({s} : Set G)) = 168) (x : G) :
    x⁻¹ * s * x ∉ T ⊓ L := by
  intro hx
  have hs2 : s * s = 1 := S.mul_self_cent hCTL hs
  have hb2 : x⁻¹ * s * x * (x⁻¹ * s * x) = 1 := by
    calc x⁻¹ * s * x * (x⁻¹ * s * x) = x⁻¹ * (s * s) * x := by group
      _ = 1 := by rw [hs2]; group
  obtain ⟨l, hl, hlb⟩ := S.exists_conj_mem_U hx.2 hb2
  set b' := l * (x⁻¹ * s * x) * l⁻¹ with hb'
  set k := l * x⁻¹ with hk
  have hb'k : b' = k * s * k⁻¹ := by rw [hb', hk]; group
  set A := fsuU T V ⊓ Subgroup.centralizer ({b'} : Set G) with hA
  have hA16 : 16 ≤ Nat.card A := S.card_cent_U hlb
  have hSyl := S.isSylowTwoOf_cent hCTL huniq hNL hs hsV h168
  set A' := A.map (MulAut.conj k⁻¹).toMonoidHom with hA'
  have hA'Z : A' ≤ Subgroup.centralizer ({s} : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hab : a * b' = b' * a := Subgroup.mem_centralizer_singleton_iff.mp ha.2
    rw [hb'k] at hab
    show k⁻¹ * a * k⁻¹⁻¹ * s = s * (k⁻¹ * a * k⁻¹⁻¹)
    calc k⁻¹ * a * k⁻¹⁻¹ * s = k⁻¹ * (a * (k * s * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * s * k⁻¹) * a) * k := by rw [hab]
      _ = s * (k⁻¹ * a * k⁻¹⁻¹) := by group
  have hU2 : IsPGroup 2 ↥(fsuU T V) := S.QU ▸ pCoreOf_isPGroup 2 (l32nH T V)
  have hA2 : IsPGroup 2 ↥A := hU2.to_le inf_le_left
  have hA'2 : IsPGroup 2 ↥A' := hA2.map _
  obtain ⟨hcomm, hsq⟩ := elem_of_le_cent hSyl (fun a ha b hb => S.comm_cent hCTL ha hb)
    (fun a ha => S.mul_self_cent hCTL ha) hA'Z hA'2
  have hconj : ∀ a ∈ A, k⁻¹ * a * k ∈ A' := fun a ha =>
    ⟨a, ha, by simp⟩
  have hel : IsElemAbelian 2 A := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
    · have h := hcomm _ (hconj a a.2) _ (hconj b b.2)
      calc (a : G) * b = k * ((k⁻¹ * a * k) * (k⁻¹ * b * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * b * k) * (k⁻¹ * a * k)) * k⁻¹ := by rw [h]
        _ = b * a := by group
    · have h := hsq _ (hconj a ha)
      rw [pow_two]
      calc a * a = k * ((k⁻¹ * a * k) * (k⁻¹ * a * k)) * k⁻¹ := by group
        _ = 1 := by rw [h]; group
  have h8 : Nat.card A ≤ 8 := S.card_le_eight (inf_le_left.trans le_sup_left) hel
  omega

theorem T_le_L (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (huniq : ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → L ⊔ T ≤ M →
      M = Subgroup.normalizer (L : Set G))
    (hNL : Subgroup.normalizer (L : Set G) = L ⊔ T) : T ≤ L := by
  by_contra hTL
  obtain ⟨t, htT, htL⟩ := IsConcreteLE.not_le_iff_exists.mp hTL
  obtain ⟨l, hl, hlt⟩ := S.exists_mem_L_conj_eq (Subgroup.mem_sup_right htT)
  have hs₀ : l⁻¹ * t ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨(L ⊔ T).mul_mem ((L ⊔ T).inv_mem (Subgroup.mem_sup_left hl))
      (Subgroup.mem_sup_right htT), Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    calc v * (l⁻¹ * t) = l⁻¹ * (l * v * l⁻¹) * l * (l⁻¹ * t) := by group
      _ = l⁻¹ * (t * v * t⁻¹) * l * (l⁻¹ * t) := by rw [hlt v hv]
      _ = l⁻¹ * t * v := by group
  have hs₀V : l⁻¹ * t ∉ V := fun h => htL (by
    rw [show t = l * (l⁻¹ * t) by group]
    exact L.mul_mem hl (S.V_le_L h))
  obtain ⟨y, hyL, hy7, u, hu, hyu⟩ := S.exists_seven
  have hfix : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1 := fun v hv h =>
    L1445.eq_one_of_fix S.card8 hy7 (S.L_le_normV hyL) hu hyu hv h
  obtain ⟨s, hs, hsV, hys⟩ := S.exists_fix_cent hyL hfix hs₀ hs₀V
  have h168 := S.card_inf_centralizer hs fun w hw =>
    S.exists_conj_cent hCTL hyL hy7 hfix hs hsV hys hw
  have hT := S.hyp.hyp.h13.sylow
  have hsT : s ∈ T := S.cent_le_T hs
  have hsTL : s ∉ T ⊓ L := fun h => hsV (S.mem_V_of_mem_cent hs h.2)
  have hs2 : s * s = 1 := S.mul_self_cent hCTL hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hos : orderOf s = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hs2) (fun h => hsV (h ▸ V.one_mem))
  have hmin : ∀ z ∈ T, z ∉ T ⊓ L → orderOf s ≤ orderOf z := by
    intro z _ hz
    have hz1 : z ≠ 1 := fun h => hz (h ▸ Subgroup.one_mem _)
    have h0 := orderOf_pos z
    have h1 : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
    omega
  obtain ⟨N, hN, hNidx⟩ := ThompsonIndexTwo.exists_normal_index_two_of_thompson hT.1 hT.2
    inf_le_left (S.relIndex_T hCTL hs hsV) hsT hsTL hmin
    (S.not_conj_mem hCTL huniq hNL hs hsV h168)
  have hsimple : IsSimpleGroup G := S.hyp.hyp.h13.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
  · rw [Subgroup.index_bot] at hNidx
    obtain ⟨a, b, hab⟩ := S.hyp.hyp.h13.nonabelian
    have := isCyclic_of_prime_card (α := G) (p := 2) hNidx
    exact hab (IsCyclic.isMulCommutative.is_comm.comm a b)
  · rw [Subgroup.index_top] at hNidx
    norm_num at hNidx

end Setup5

end L1444

open L1444 in
theorem lemma1445One_of_inputs (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hRest : Lemma14323Rest) (hCTL : Lemma1444CTL) : Lemma1445One := by
  intro G _ _ T L V h hext h32 hG2
  classical
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, g, hV₂, hgP, hgH⟩ := h.exists_plane_and_g h13322 hV (exist1282g h1222)
  obtain ⟨D, Q₁, Q₂, S⟩ := exists_setup5 h1332 h1334 h1222 h12213 h37 h38 h39 hRest hCTL h hext
    h32 hG2 hV₂ hgP hgH
  have hNL := (lemma1444Seven_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest G T L V h
    hext h32 hG2).2
  have hL13 := h1332 G T L h.hyp.h13 L h.hyp.h13.faithful
  rw [hNL]
  exact sup_eq_left.mpr (S.T_le_L (hCTL G T L V h hext h32 hG2) hL13.2.1.2.2.2 hNL)

end CFSG.Quasithin.H13
