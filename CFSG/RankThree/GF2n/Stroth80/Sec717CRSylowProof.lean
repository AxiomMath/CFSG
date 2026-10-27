module

public import CFSG.RankThree.GF2n.Stroth80.Sec717OrbitOdd
public import CFSG.RankThree.GF2n.Stroth80.Sec717NormSylowProof
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsLinear
import CFSG.RankThree.GF2n.Stroth80.Sec7TailRecogCtx

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

section Group

variable {X : Type*} [Group X]

theorem card_eq_card_mul_card_inf_centralizer [Finite X] {N W : Subgroup X} {x : X}
    (hW : ∀ m ∈ N, m * x * m⁻¹ * x⁻¹ ∈ W) (hsurj : ∀ w ∈ W, ∃ m ∈ N, m * x * m⁻¹ = w * x) :
    Nat.card N = Nat.card W * Nat.card ↥(N ⊓ centralizer ({x} : Set X)) := by
  let C : Subgroup ↥N := (centralizer ({x} : Set X)).subgroupOf N
  have hCcard : Nat.card C = Nat.card ↥(N ⊓ centralizer ({x} : Set X)) :=
    Nat.card_congr
      { toFun := fun c => ⟨c.1.1, c.1.2, c.2⟩
        invFun := fun d => ⟨⟨d.1, d.2.1⟩, d.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have key : ∀ a b : X, a * x * a⁻¹ = b * x * b⁻¹ ↔ (a⁻¹ * b) * x = x * (a⁻¹ * b) := by
    intro a b
    constructor
    · intro h
      calc (a⁻¹ * b) * x = a⁻¹ * (b * x * b⁻¹) * b := by group
        _ = a⁻¹ * (a * x * a⁻¹) * b := by rw [h]
        _ = x * (a⁻¹ * b) := by group
    · intro h
      calc a * x * a⁻¹ = a * (x * (a⁻¹ * b)) * b⁻¹ := by group
        _ = a * ((a⁻¹ * b) * x) * b⁻¹ := by rw [h]
        _ = b * x * b⁻¹ := by group
  let f : ↥N → ↥W := fun m => ⟨(m : X) * x * (m : X)⁻¹ * x⁻¹, hW m m.2⟩
  have hf : ∀ a b : ↥N, f a = f b ↔ a⁻¹ * b ∈ C := by
    intro a b
    rw [Subtype.ext_iff, mul_left_inj, key, mem_subgroupOf, mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  let F : ↥N ⧸ C → ↥W :=
    Quotient.lift f fun a b hab => (hf a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  have hFbij : Function.Bijective F := by
    constructor
    · intro u v huv
      induction u using Quotient.inductionOn with
      | h a =>
        induction v using Quotient.inductionOn with
        | h b => exact QuotientGroup.eq.mpr ((hf a b).mp huv)
    · intro w
      obtain ⟨m, hm, hmw⟩ := hsurj w w.2
      refine ⟨QuotientGroup.mk ⟨m, hm⟩, Subtype.ext ?_⟩
      change m * x * m⁻¹ * x⁻¹ = (w : X)
      rw [hmw, mul_inv_cancel_right]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup C,
    Nat.card_congr (Equiv.ofBijective F hFbij), hCcard]

end Group

section Line

variable {Γ K E : Type*} [Group Γ] [Field K] [AddCommGroup E] [Module K E]

theorem comm_of_comm_of_line (ρ : Γ →* Multiplicative (AddAut E))
    (hρ : ∀ a a' : Γ, (∀ e, (ρ a).toAdd e = (ρ a').toAdd e) → a = a')
    {V : Subgroup Γ} {a₁ : Γ}
    (hV : ∀ a ∈ V, ∃ c : K, ∀ e, (ρ a).toAdd e = e + c • ((ρ a₁).toAdd e - e))
    {x : Γ} (hx : ∀ (c : K) (e : E), (ρ x).toAdd (c • e) = c • (ρ x).toAdd e)
    (hxa : x * a₁ = a₁ * x) : ∀ a ∈ V, x * a = a * x := by
  have hone : ∀ e, (ρ 1).toAdd e = e := fun e => by
    rw [map_one]
    rfl
  have hmul : ∀ (a b : Γ) (e : E), (ρ (a * b)).toAdd e = (ρ a).toAdd ((ρ b).toAdd e) :=
    fun a b e => by
      rw [map_mul]
      rfl
  have hinv : ∀ (g : Γ) (e : E), (ρ g).toAdd ((ρ g⁻¹).toAdd e) = e := fun g e => by
    rw [← hmul, mul_inv_cancel, hone]
  have hxa' : x * a₁ * x⁻¹ = a₁ := by rw [hxa, mul_inv_cancel_right]
  intro a ha
  obtain ⟨c, hc⟩ := hV a ha
  have h := hρ (x * a * x⁻¹) a fun e => by
    have h1 : (ρ (x * a * x⁻¹)).toAdd e =
        e + c • ((ρ (x * a₁ * x⁻¹)).toAdd e - e) := by
      simp only [hmul]
      rw [hc, map_add, hx, map_sub, hinv]
    rw [h1, hxa', hc e]
  exact mul_inv_eq_iff_eq_mul.mp h

end Line

section Ctx

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.comm_Z0_of_comm (h34 : Stroth34Statement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∀ x ∈ bar M Q (H0 M Z), ∀ v₀ ∈ bar M Q Z0, v₀ ≠ 1 → x * v₀ = v₀ * x →
      ∀ v ∈ bar M Q Z0, x * v = v * x := by
  intro x hx v₀ hv₀ hv₀1 hxv₀
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, -, hρ, ψ, -, -, hA, -⟩ :=
    sec7_linModelData h34 (stroth310Chi_of_34 h34) hc hs hZ0
      (fun z hz w hw => (hZc G M Q Z B hc n t hs Z0 hZ0 z hz).2 w hw)
      (fun u hu huQ => hZV G M Q Z B hc n t hs Z0 hZ0 u hu huQ)
  obtain ⟨c₀, hc₀⟩ := hA v₀ hv₀
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    refine hv₀1 (hρ v₀ 1 fun e => ?_)
    rw [hc₀ e, zero_smul, add_zero, map_one]
    rfl
  have hV : ∀ a ∈ bar M Q Z0, ∃ c : K, ∀ e, (ρ a).toAdd e = e + c • ((ρ v₀).toAdd e - e) := by
    intro a ha
    obtain ⟨c, hc⟩ := hA a ha
    refine ⟨c * c₀⁻¹, fun e => ?_⟩
    rw [hc e, hc₀ e, add_sub_cancel_left, smul_smul, mul_assoc, inv_mul_cancel₀ hc₀0, mul_one]
  exact comm_of_comm_of_line ρ hρ hV (fun c e => hS.lin x hx c e) hxv₀

end Ctx

section Frame

variable {K E : Type*} {X : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Group X] {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)}
  {V L Nb Rb : Subgroup X} {Tt : X → Submodule K E} {q : ℕ}

theorem MoveFrame.exists_sylow_conj_normalizes_L [Finite X] (F : MoveFrame B φ V L Nb Rb Tt q)
    (hVc : ∀ r ∈ Rb, ∀ a ∈ V, r * a = a * r)
    (hline : ∀ x : X, ∀ v₀ ∈ V, v₀ ≠ 1 → x * v₀ = v₀ * x → ∀ v ∈ V, x * v = v * x)
    {z h : X} (hz : z ∈ V) (hz1 : z ≠ 1) (hyL : h * z * h⁻¹ ∈ L) (hyV : h * z * h⁻¹ ∉ V)
    (hodd : Odd (((Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)) ⊔ Nb).subgroupOf Rb).index) :
    ∃ T : Sylow 2 ↥(conjSubgroup h Rb),
      Subgroup.map (conjSubgroup h Rb).subtype T ≤ normalizer (L : Set X) := by
  have mc : ∀ {S : Subgroup X} {x : X}, x ∈ conjSubgroup h S ↔ h⁻¹ * x * h ∈ S :=
    CFSG.CGT.Timmesfeld75.mem_conjSubgroup
  have hconj_mem : ∀ {S : Subgroup X} {x : X}, x ∈ S → h * x * h⁻¹ ∈ conjSubgroup h S :=
    fun {S x} hx => mc.mpr (by simpa [mul_assoc] using hx)
  have hV2 : IsPGroup 2 V := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, pow_two, Subgroup.coe_mul, F.V_sq _ g.2]
    rfl)⟩
  have hVh2 : IsPGroup 2 (conjSubgroup h V) := hV2.map (MulAut.conj h).toMonoidHom
  have hNh2 : IsPGroup 2 (conjSubgroup h Nb) := F.Nb_pgroup.map (MulAut.conj h).toMonoidHom
  have hRhNh : ∀ r ∈ conjSubgroup h Rb, r ∈ normalizer (conjSubgroup h Nb : Set X) := by
    intro r hr
    have key : ∀ r ∈ conjSubgroup h Rb, ∀ n ∈ conjSubgroup h Nb,
        r * n * r⁻¹ ∈ conjSubgroup h Nb := by
      intro r hr n hn
      refine mc.mpr ?_
      have e : h⁻¹ * (r * n * r⁻¹) * h =
          (h⁻¹ * r * h) * (h⁻¹ * n * h) * (h⁻¹ * r * h)⁻¹ := by group
      rw [e]
      exact F.conj_mem_Nb (mc.mp hr) (mc.mp hn)
    refine mem_normalizer_iff.mpr fun n => ⟨key r hr n, fun hn => ?_⟩
    simpa [mul_assoc] using key r⁻¹ (inv_mem hr) _ hn
  obtain ⟨hNg, hcommL⟩ := F.L_comm_Vg z h hz hz1 hyL hyV
  have hLNh : ∀ l ∈ L, l ∈ conjSubgroup h Nb := F.L_le_Nbg z h hz hz1 hyL hyV hNg hcommL
  have hVhL : conjSubgroup h V ≤ L := by
    intro v hv
    have hvc : ∀ a ∈ V, v * a = a * v := fun a ha => (hcommL a (F.V_le_L ha) v hv).symm
    have hvN : v ∈ normalizer (V : Set X) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun a ha => (hvc a ha).symm)
    have hv2 : IsPGroup 2 (zpowers v) := hVh2.to_le (zpowers_le.mpr hv)
    exact F.CL v (F.two_elements v hvN hvc hv2) fun l hl => (hcommL l hl v hv).symm
  have hNhL : ∀ m ∈ conjSubgroup h Nb, m ∈ normalizer (L : Set X) := by
    have key : ∀ m ∈ conjSubgroup h Nb, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
      intro m hm l hl
      have hc : ⁅m, l⁆ ∈ conjSubgroup h V := by
        refine mc.mpr ?_
        have e : h⁻¹ * ⁅m, l⁆ * h = ⁅h⁻¹ * m * h, h⁻¹ * l * h⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact F.Nb_comm _ (mc.mp hm) _ (mc.mp (hLNh l hl))
      have e : m * l * m⁻¹ = ⁅m, l⁆ * l := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact L.mul_mem (hVhL hc) hl
    intro m hm
    refine mem_normalizer_iff.mpr fun l => ⟨key m hm l, fun hl => ?_⟩
    simpa [mul_assoc] using key m⁻¹ (inv_mem hm) _ hl
  have hzVh : z ∉ conjSubgroup h V := by
    intro hzh
    have h1 : h⁻¹ * z * h⁻¹⁻¹ ∈ V := by simpa using mc.mp hzh
    have hN := F.ti h⁻¹ z hz hz1 h1
    have hN' : h ∈ normalizer (V : Set X) := by simpa using inv_mem hN
    exact hyV ((mem_normalizer_iff.mp hN' z).mp hz)
  have hCVh : ∀ c : X, c * (h * z * h⁻¹) = (h * z * h⁻¹) * c →
      ∀ v ∈ conjSubgroup h V, c * v = v * c := by
    intro c hc v hv
    have h1 : (h⁻¹ * c * h) * z = z * (h⁻¹ * c * h) := by
      calc (h⁻¹ * c * h) * z = h⁻¹ * (c * (h * z * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * z * h⁻¹) * c) * h := by rw [hc]
        _ = z * (h⁻¹ * c * h) := by group
    have h2 := hline _ z hz hz1 h1 _ (mc.mp hv)
    calc c * v = h * ((h⁻¹ * c * h) * (h⁻¹ * v * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * v * h) * (h⁻¹ * c * h)) * h⁻¹ := by rw [h2]
      _ = v * c := by group
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 ↥(Rb ⊓ centralizer ({h * z * h⁻¹} : Set X))) := Sylow.nonempty
  have hT₀C : Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ≤
      Rb ⊓ centralizer ({h * z * h⁻¹} : Set X) := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hT₀2 : IsPGroup 2 (Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀) :=
    T₀.isPGroup'.map _
  have hT₀Rh : Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ≤
      conjSubgroup h Rb := by
    intro c hc
    have hcC := hT₀C hc
    have hcy : c * (h * z * h⁻¹) = (h * z * h⁻¹) * c :=
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hcC).2)
    have hcV : ∀ a ∈ V, (h⁻¹ * c * h) * a = a * (h⁻¹ * c * h) := by
      intro a ha
      have := hCVh c hcy _ (hconj_mem ha)
      calc (h⁻¹ * c * h) * a = h⁻¹ * (c * (h * a * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * a * h⁻¹) * c) * h := by rw [this]
        _ = a * (h⁻¹ * c * h) := by group
    have hcN : h⁻¹ * c * h ∈ normalizer (V : Set X) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun a ha => (hcV a ha).symm)
    have hc2 : IsPGroup 2 (zpowers (h⁻¹ * c * h)) := by
      have h1 : IsPGroup 2 (conjSubgroup h⁻¹
          (Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀)) :=
        hT₀2.map (MulAut.conj h⁻¹).toMonoidHom
      refine h1.to_le (zpowers_le.mpr ?_)
      refine CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr ?_
      simpa [mul_assoc] using hc
    exact mc.mpr (F.two_elements _ hcN hcV hc2)
  have hT₀L : Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ≤
      normalizer (L : Set X) := fun c hc =>
    F.mem_normalizer_L (F.Rb_le_K c (mem_inf.mp (hT₀C hc)).1)
  have hT₀Nh : Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ≤
      normalizer (conjSubgroup h Nb : Set X) := fun c hc => hRhNh c (hT₀Rh hc)
  have hD : Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ⊓
      conjSubgroup h Nb = conjSubgroup h Nb ⊓ centralizer (V : Set X) := by
    apply le_antisymm
    · intro c hc
      obtain ⟨hcT, hcN⟩ := mem_inf.mp hc
      refine mem_inf.mpr ⟨hcN, mem_centralizer_iff.mpr fun a ha => ?_⟩
      exact (hVc c (mem_inf.mp (hT₀C hcT)).1 a ha).symm
    ·
      have hDC : conjSubgroup h Nb ⊓ centralizer (V : Set X) ≤
          Rb ⊓ centralizer ({h * z * h⁻¹} : Set X) := by
        intro c hc
        obtain ⟨hcN, hcV⟩ := mem_inf.mp hc
        have hcV' : ∀ a ∈ V, c * a = a * c := fun a ha => (mem_centralizer_iff.mp hcV a ha).symm
        have hcNV : c ∈ normalizer (V : Set X) := centralizer_le_normalizer _ hcV
        have hc2 : IsPGroup 2 (zpowers c) := hNh2.to_le (zpowers_le.mpr hcN)
        refine mem_inf.mpr ⟨F.two_elements c hcNV hcV' hc2, ?_⟩
        refine mem_centralizer_singleton_iff.mpr ?_
        have hn : h⁻¹ * c * h ∈ Nb := mc.mp hcN
        have := hVc _ (F.Nb_le_Rb hn) z hz
        calc c * (h * z * h⁻¹) = h * ((h⁻¹ * c * h) * z) * h⁻¹ := by group
          _ = h * (z * (h⁻¹ * c * h)) * h⁻¹ := by rw [this]
          _ = (h * z * h⁻¹) * c := by group
      have hD2 : IsPGroup 2 ↥(conjSubgroup h Nb ⊓ centralizer (V : Set X) : Subgroup X) :=
        hNh2.to_le inf_le_left
      have hTD : Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ≤
          normalizer ((conjSubgroup h Nb ⊓ centralizer (V : Set X) : Subgroup X) : Set X) := by
        intro c hc
        have hcN := hT₀Nh hc
        have hcV : c ∈ centralizer (V : Set X) :=
          mem_centralizer_iff.mpr fun a ha => (hVc c (mem_inf.mp (hT₀C hc)).1 a ha).symm
        refine mem_normalizer_iff.mpr fun d => ?_
        rw [mem_inf, mem_inf, (mem_normalizer_iff.mp hcN d)]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, (centralizer (V : Set X)).mul_mem
            ((centralizer (V : Set X)).mul_mem hcV h2) (inv_mem hcV)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          have := (centralizer (V : Set X)).mul_mem
            ((centralizer (V : Set X)).mul_mem (inv_mem hcV) h2) hcV
          simpa [mul_assoc] using this
      have hE2 := IsPGroup.to_sup_of_normal_right' hT₀2 hD2 hTD
      have hEC := sup_le hT₀C hDC
      have hmax := T₀.is_maximal' (Q := (Subgroup.map
          (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ⊔
            (conjSubgroup h Nb ⊓ centralizer (V : Set X))).subgroupOf
          (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)))
        hE2.comap_subtype (fun c hc => mem_subgroupOf.mpr (mem_sup_left ⟨c, hc, rfl⟩))
      intro d hd
      have hdC := hDC hd
      have hd' : (⟨d, hdC⟩ : ↥(Rb ⊓ centralizer ({h * z * h⁻¹} : Set X))) ∈
          (T₀ : Subgroup ↥(Rb ⊓ centralizer ({h * z * h⁻¹} : Set X))) := by
        rw [← hmax]
        exact mem_subgroupOf.mpr (mem_sup_right hd)
      exact mem_inf.mpr ⟨⟨_, hd', rfl⟩, (mem_inf.mp hd).1⟩
  have hVcard : Nat.card ↥(conjSubgroup h V) = Nat.card V := natCard_conjSubgroup h V
  have hyNb : h * z * h⁻¹ ∈ Nb := F.L_le_Nb hyL
  have hNb : Nat.card Nb = Nat.card V * Nat.card ↥(Nb ⊓ centralizer ({h * z * h⁻¹} : Set X)) := by
    refine card_eq_card_mul_card_inf_centralizer (fun m hm => ?_) fun w hw => ?_
    · have := F.Nb_comm m hm _ hyNb
      rwa [commutatorElement_def] at this
    · exact F.Nb_semi _ hyNb hyV w hw
  have hzNh : z ∈ conjSubgroup h Nb := hLNh z (F.V_le_L hz)
  have hNh : Nat.card ↥(conjSubgroup h Nb) =
      Nat.card V * Nat.card ↥(conjSubgroup h Nb ⊓ centralizer (V : Set X)) := by
    have hcz : conjSubgroup h Nb ⊓ centralizer ({z} : Set X) =
        conjSubgroup h Nb ⊓ centralizer (V : Set X) := by
      ext c
      simp only [mem_inf, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun a ha => (hline c z hz hz1 h2.symm a ha).symm⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2 z hz⟩
    rw [← hcz, ← hVcard]
    refine card_eq_card_mul_card_inf_centralizer (fun m hm => ?_) fun w hw => ?_
    · have := F.Nb_comm _ (mc.mp hm) _ (mc.mp hzNh)
      refine mc.mpr ?_
      have e : h⁻¹ * (m * z * m⁻¹ * z⁻¹) * h = ⁅h⁻¹ * m * h, h⁻¹ * z * h⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact this
    · have hz' : h⁻¹ * z * h ∉ V := fun h1 => hzVh (mc.mpr h1)
      obtain ⟨m, hm, hmz⟩ := F.Nb_semi _ (mc.mp hzNh) hz' _ (mc.mp hw)
      refine ⟨h * m * h⁻¹, hconj_mem hm, ?_⟩
      calc h * m * h⁻¹ * z * (h * m * h⁻¹)⁻¹ = h * (m * (h⁻¹ * z * h) * m⁻¹) * h⁻¹ := by group
        _ = h * ((h⁻¹ * w * h) * (h⁻¹ * z * h)) * h⁻¹ := by rw [hmz]
        _ = w * z := by group
  have hCNb : Rb ⊓ centralizer ({h * z * h⁻¹} : Set X) ≤ normalizer (Nb : Set X) := by
    intro c hc
    refine mem_normalizer_iff.mpr fun n => ⟨fun hn => F.conj_mem_Nb (mem_inf.mp hc).1 hn,
      fun hn => ?_⟩
    simpa [mul_assoc] using F.conj_mem_Nb (inv_mem (mem_inf.mp hc).1) hn
  have hA : Nat.card ↥((Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)) ⊔ Nb) =
      Nat.card ↥(Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)) * Nat.card V := by
    have hprod := card_sup_mul_card_inf_of_le_normalizer hCNb
    have hinf : Nb ⊓ (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)) =
        Nb ⊓ centralizer ({h * z * h⁻¹} : Set X) := by
      ext c
      simp only [mem_inf]
      exact ⟨fun h1 => ⟨h1.1, h1.2.2⟩, fun h1 => ⟨h1.1, F.Nb_le_Rb h1.1, h1.2⟩⟩
    rw [hinf, hNb, sup_comm] at hprod
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hprod]; ring)
  have hT : Nat.card ↥(Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ⊔
      conjSubgroup h Nb) = Nat.card T₀ * Nat.card V := by
    have hprod := card_sup_mul_card_inf_of_le_normalizer hT₀Nh
    rw [inf_comm (conjSubgroup h Nb), hD, hNh,
      Subgroup.card_map_of_injective Subtype.coe_injective, sup_comm (conjSubgroup h Nb)]
      at hprod
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hprod]; ring)
  have hTRh : Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ⊔
      conjSubgroup h Nb ≤ conjSubgroup h Rb :=
    sup_le hT₀Rh fun n hn => mc.mpr (F.Nb_le_Rb (mc.mp hn))
  have hT2 : IsPGroup 2 ((Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ⊔
      conjSubgroup h Nb).subgroupOf (conjSubgroup h Rb)) :=
    (IsPGroup.to_sup_of_normal_right' hT₀2 hNh2 hT₀Nh).comap_subtype
  have hidx : ¬ 2 ∣ ((Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ⊔
      conjSubgroup h Nb).subgroupOf (conjSubgroup h Rb)).index := by
    obtain ⟨o₁, ho₁⟩ := hodd
    have hRb := Subgroup.card_mul_index
      (((Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)) ⊔ Nb).subgroupOf Rb)
    rw [Nat.card_congr (subgroupOfEquivOfLe (sup_le inf_le_left F.Nb_le_Rb)).toEquiv, hA,
      ho₁] at hRb
    have hC := Subgroup.card_mul_index (T₀ : Subgroup ↥(Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)))
    have hT₀odd := T₀.not_dvd_index
    have hRh := Subgroup.card_mul_index ((Subgroup.map
      (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ⊔ conjSubgroup h Nb).subgroupOf
        (conjSubgroup h Rb))
    rw [Nat.card_congr (subgroupOfEquivOfLe hTRh).toEquiv, hT, natCard_conjSubgroup, ← hRb,
      ← hC] at hRh
    have hpos : 0 < Nat.card T₀ * Nat.card V := Nat.mul_pos Nat.card_pos Nat.card_pos
    have hi : ((Subgroup.map (Rb ⊓ centralizer ({h * z * h⁻¹} : Set X)).subtype T₀ ⊔
        conjSubgroup h Nb).subgroupOf (conjSubgroup h Rb)).index =
        (T₀ : Subgroup ↥(Rb ⊓ centralizer ({h * z * h⁻¹} : Set X))).index * (2 * o₁ + 1) :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [hRh]; ring)
    rw [hi]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h3 | h3
    · exact hT₀odd h3
    · omega
  refine ⟨hT2.toSylow hidx, ?_⟩
  rw [IsPGroup.toSylow_coe, Subgroup.map_le_iff_le_comap]
  intro x hx
  exact sup_le hT₀L hNhL (mem_subgroupOf.mp hx)

end Frame


theorem sec717CRSylow_of_orbitOdd (hF : Sec717MoveFrameStatement) (h34 : Stroth34Statement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hOrb : Sec717OrbitOddStatement) :
    Sec717CRSylowStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn hex hLK z hz hz1 h hhz hhzV
  obtain ⟨K, _, E, _, _, _, B', φ, Tt, q, F⟩ :=
    hF G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn
  have hVc : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), r * a = a * r := fun r hr a ha =>
    Subtype.ext (hc.recog_bar_Z0_comm hZ0 _ (mem_subgroupOf.mp ha) _
      (mem_subgroupOf.mp hr)).symm
  have hline : ∀ x : ↥(bar M Q (H0 M Z)), ∀ v₀ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      v₀ ≠ 1 → x * v₀ = v₀ * x →
        ∀ v ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), x * v = v * x := by
    intro x v₀ hv₀ hv₀1 hxv v hv
    exact Subtype.ext (hc.comm_Z0_of_comm h34 hZc hZV hs hZ0 x x.2 v₀ (mem_subgroupOf.mp hv₀)
      (fun h1 => hv₀1 (Subtype.ext h1)) (congrArg Subtype.val hxv) v (mem_subgroupOf.mp hv))
  exact F.exists_sylow_conj_normalizes_L hVc hline hz hz1 hhz hhzV
    (hOrb G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn _ hhz hhzV)

end CFSG.RankThree.GF2n.Stroth80
