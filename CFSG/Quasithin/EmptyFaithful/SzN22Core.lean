module

public import CFSG.Quasithin.EmptyFaithful.SzN22Basic
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SzN22

variable {Ω : Type} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem normalized_of_theta {Y M : Subgroup Ω}
    (hYgen : Y = Subgroup.closure {y | y ∈ Y ∧ orderOf y = 3}) (hYM : Y ≤ M)
    (hθ : ∀ x ∈ M, orderOf x = 3 → x ∈ Y) : ∀ m ∈ M, ∀ y ∈ Y, m * y * m⁻¹ ∈ Y := by
  intro m hm y hy
  rw [hYgen] at hy
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨hgY, hg3⟩ := hg
    refine hθ _ (M.mul_mem (M.mul_mem hm (hYM hgY)) (M.inv_mem hm)) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hg3
  | one => simp
  | mul a b _ _ iha ihb =>
    have := Y.mul_mem iha ihb
    simpa [mul_assoc] using this
  | inv a _ iha =>
    have := Y.inv_mem iha
    simpa [mul_assoc] using this

theorem k_core {Hs Ts Ys Ms K C : Subgroup Ω}
    (hKC : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a) (hinf : K ⊓ C = ⊥)
    (hKns : ¬ Group.IsSolvable ↥K) (hKH : K ≤ Hs) (hCH : C ≤ Hs)
    (hHL : Hs ≤ Subgroup.normalizer ((K ⊔ C : Subgroup Ω) : Set Ω))
    (hO2 : pCoreOf 2 Hs = ⊥) (hTs : IsSylowTwoOf Ts Hs)
    (hYM : Ys ≤ Ms) (hMH : Ms ≤ Hs) (hTY : Ts ≤ Subgroup.normalizer (Ys : Set Ω))
    (hord : ∀ y ∈ Ys, ∃ k : ℕ, y ^ (2 ^ k * 3) = 1) (hex : ∃ y ∈ Ys, orderOf y = 3)
    (hY3 : ∀ E : Subgroup Ω, E ≤ Ys → IsPGroup 3 E → Nat.card E ≤ 3)
    (hYgen : Ys = Subgroup.closure {y | y ∈ Ys ∧ orderOf y = 3})
    (hθ : ∀ x ∈ Ms, orderOf x = 3 → x ∈ Ys)
    (hmin : ∀ K' : Subgroup Ω, Ys ⊔ Ts ≤ K' → K' ≤ Hs → K' ≠ Hs → K' ≤ Ms)
    (hYK : Ys ≤ Subgroup.normalizer (K : Set Ω)) (hKY : ⁅K, Ys⁆ = K)
    (hRig : ∀ (S : Subgroup Ω) (z : Ω), IsSylowTwoOf S K → z ∈ Subgroup.normalizer (K : Set Ω) →
      z ∈ Subgroup.normalizer (S : Set Ω) → z ^ 3 = 1 →
      (∀ b ∈ Subgroup.normalizer (S : Set Ω) ⊓ K, orderOf b ≠ 3) →
      (∀ b ∈ Subgroup.normalizer (S : Set Ω) ⊓ K, z * b * z⁻¹ * b⁻¹ ∈ S) →
      ∃ x ∈ K, ∀ n ∈ K, z * n * z⁻¹ = x * n * x⁻¹) :
    Ys ≤ K ⊔ C := by
  by_contra hYL
  set L₀ : Subgroup Ω := K ⊔ C with hL₀
  have hL₀H : L₀ ≤ Hs := sup_le hKH hCH
  have hYH : Ys ≤ Hs := hYM.trans hMH
  have hTH : Ts ≤ Hs := hTs.1
  have hHLn : ∀ g ∈ Hs, ∀ q ∈ L₀, g * q * g⁻¹ ∈ L₀ := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hHL hg) q).mp hq
  have hYn : ∀ y ∈ Ys, ∀ q ∈ L₀, y * q * y⁻¹ ∈ L₀ := fun y hy => hHLn y (hYH hy)
  have hno3 : ∀ b ∈ Ys, b ∈ L₀ → orderOf b ≠ 3 := fun b hbY hbL hb3 =>
    hYL (le_of_orderThree_mem hYgen hY3 hYn hbY hbL hb3)
  obtain ⟨m, hm⟩ := hTs.2.1.exists_card_eq
  have hcardP : Nat.card ↥(Ys ⊔ Ts) = 3 * 2 ^ m := by
    rw [SzN19.card_sup_eq_three_mul hTs hYH hTY hord hex hY3, hm]
  have hpowP : ∀ x ∈ Ys ⊔ Ts, x ^ (2 ^ m * 3) = 1 := by
    intro x hx
    have := pow_card_eq_one' (G := ↥(Ys ⊔ Ts)) (x := (⟨x, hx⟩ : ↥(Ys ⊔ Ts)))
    rw [hcardP] at this
    have h2 := congrArg Subtype.val this
    simpa [mul_comm] using h2
  have hTn : Ts ≤ Subgroup.normalizer (L₀ : Set Ω) := fun t ht => hHL (hTH ht)
  have hS₀ : IsSylowTwoOf (Ts ⊓ L₀) L₀ := isSylowTwoOf_inf_normalized hTs hL₀H hTn
  have hD2 : IsPGroup 2 ↥((Ys ⊔ Ts) ⊓ L₀) := by
    refine isPGroup_two_of_no_orderThree m (fun x hx => hpowP x hx.1) fun x hx hx3 => ?_
    have hx3' : x ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one x
    exact hno3 x (mem_of_pow_three_sup hTs.2.1 hTY hx.1 hx3') hx.2 hx3
  have hDS : (Ys ⊔ Ts) ⊓ L₀ = Ts ⊓ L₀ :=
    eq_of_isSylowTwoOf_le hS₀ (inf_le_inf_right _ le_sup_right) inf_le_right hD2
  set S₀ : Subgroup Ω := Ts ⊓ L₀ with hS₀def
  have hPn : Ys ⊔ Ts ≤ Subgroup.normalizer (S₀ : Set Ω) := by
    intro g hg
    have h1 : g ∈ Subgroup.normalizer ((Ys ⊔ Ts : Subgroup Ω) : Set Ω) := Subgroup.le_normalizer hg
    have h2 : g ∈ Subgroup.normalizer (L₀ : Set Ω) := hHL (sup_le hYH hTH hg)
    have h3 := Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
    rwa [hDS] at h3
  have hS₀ne : S₀ ≠ ⊥ := by
    intro h0
    have h1 := hS₀.2.2
    rw [h0, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h1
    have hodd : Odd (Nat.card ↥L₀) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h1)
    have hsolv : Group.IsSolvable ↥L₀ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    exact hKns (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (le_sup_left : K ≤ L₀)) (Subgroup.inclusion_injective _))
  have hPne : Subgroup.normalizer (S₀ : Set Ω) ⊓ Hs ≠ Hs := by
    intro hP
    apply hS₀ne
    have hnorm : Hs ≤ Subgroup.normalizer (S₀ : Set Ω) := inf_eq_right.mp hP
    have := le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hTH) hnorm hS₀.2.1
    rw [hO2] at this
    exact le_bot_iff.mp this
  have hPYT : Ys ⊔ Ts ≤ Subgroup.normalizer (S₀ : Set Ω) ⊓ Hs := le_inf hPn (sup_le hYH hTH)
  have hPM := hmin _ hPYT inf_le_right hPne
  have hB₀no3 : ∀ b ∈ Subgroup.normalizer (S₀ : Set Ω) ⊓ L₀, orderOf b ≠ 3 := by
    intro b hb hb3
    have hbM : b ∈ Ms := hPM ⟨hb.1, hL₀H hb.2⟩
    exact hno3 b (hθ b hbM hb3) hb.2 hb3
  have hCK : C ≤ Subgroup.normalizer (K : Set Ω) := SzN19.le_normalizer_of_commute hKC
  have hKn : K ≤ Subgroup.normalizer (C : Set Ω) :=
    SzN19.le_normalizer_of_commute fun a ha b hb => (hKC b hb a ha).symm
  have hS₀K : S₀ ≤ Subgroup.normalizer (K : Set Ω) :=
    inf_le_right.trans (sup_le Subgroup.le_normalizer hCK)
  have hS₀C : S₀ ≤ Subgroup.normalizer (C : Set Ω) :=
    inf_le_right.trans (sup_le hKn Subgroup.le_normalizer)
  have hSK : IsSylowTwoOf (S₀ ⊓ K) K := by
    have h1 : IsSylowTwoOf S₀ (K ⊔ S₀) :=
      isSylowTwoOf_of_le hS₀ le_sup_right (sup_le le_sup_left inf_le_right)
    exact SzN19.isSylowTwoOf_inf_of_normalizes h1 le_sup_left hS₀K le_rfl
  have hπ2 : IsPGroup 2 ↥((C ⊔ S₀) ⊓ K) := isPGroup_proj hinf (hTs.2.1.to_le inf_le_left) hS₀C
  have hπ : (C ⊔ S₀) ⊓ K = S₀ ⊓ K :=
    eq_of_isSylowTwoOf_le hSK (inf_le_inf_right K le_sup_right) inf_le_right hπ2
  have hBK : ∀ b ∈ Subgroup.normalizer ((S₀ ⊓ K : Subgroup Ω) : Set Ω) ⊓ K,
      b ∈ Subgroup.normalizer (S₀ : Set Ω) := by
    have key : ∀ b' ∈ Subgroup.normalizer ((S₀ ⊓ K : Subgroup Ω) : Set Ω) ⊓ K, ∀ s ∈ S₀,
        b' * s * b'⁻¹ ∈ S₀ := by
      intro b' hb' s hs
      have hsL : s ∈ K ⊔ C := hs.2
      obtain ⟨k, hk, c, hc, hsk⟩ := SzN19.exists_mul_of_normalizes hCK hsL
      have hkeq : k = s * c⁻¹ := by rw [hsk]; group
      have hk1 : k ∈ C ⊔ S₀ := by
        rw [hkeq]
        exact (C ⊔ S₀).mul_mem (Subgroup.mem_sup_right hs)
          ((C ⊔ S₀).inv_mem (Subgroup.mem_sup_left hc))
      have hkπ : k ∈ (C ⊔ S₀) ⊓ K := ⟨hk1, hk⟩
      rw [hπ] at hkπ
      have hkS : k ∈ S₀ := hkπ.1
      have hcS : c ∈ S₀ := by
        have : c = k⁻¹ * s := by rw [hsk]; group
        rw [this]
        exact S₀.mul_mem (S₀.inv_mem hkS) hs
      have hbk : b' * k * b'⁻¹ ∈ S₀ ⊓ K := (Subgroup.mem_normalizer_iff.mp hb'.1 k).mp hkπ
      have hbc : b' * c = c * b' := hKC b' hb'.2 c hc
      have e : b' * s * b'⁻¹ = (b' * k * b'⁻¹) * c := by
        have h2 : b' * c * b'⁻¹ = c := by rw [hbc]; group
        calc b' * s * b'⁻¹ = b' * (k * c) * b'⁻¹ := by rw [← hsk]
          _ = (b' * k * b'⁻¹) * (b' * c * b'⁻¹) := by group
          _ = (b' * k * b'⁻¹) * c := by rw [h2]
      rw [e]
      exact S₀.mul_mem hbk.1 hcS
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => key b hb s hs, fun hs => ?_⟩
    have hb' : b⁻¹ ∈ Subgroup.normalizer ((S₀ ⊓ K : Subgroup Ω) : Set Ω) ⊓ K :=
      ⟨Subgroup.inv_mem _ hb.1, K.inv_mem hb.2⟩
    have := key b⁻¹ hb' _ hs
    simpa [mul_assoc] using this
  have hBK3 : ∀ b ∈ Subgroup.normalizer ((S₀ ⊓ K : Subgroup Ω) : Set Ω) ⊓ K, orderOf b ≠ 3 :=
    fun b hb => hB₀no3 b ⟨hBK b hb, (le_sup_left : K ≤ K ⊔ C) hb.2⟩
  have hYMn := normalized_of_theta hYgen hYM hθ
  obtain ⟨a, ha⟩ := SzN19.card_eq_two_pow_mul_three hord hex hY3
  have hpowY : ∀ x ∈ Ys, x ^ (2 ^ a * 3) = 1 := by
    intro x hx
    have := pow_card_eq_one' (G := ↥Ys) (x := (⟨x, hx⟩ : ↥Ys))
    rw [ha] at this
    exact congrArg Subtype.val this
  have hz : ∀ z ∈ Ys, z ^ 3 = 1 → ∀ n ∈ K, z * n * z⁻¹ = n := by
    intro z hzY hz3
    have hzK : z ∈ Subgroup.normalizer (K : Set Ω) := hYK hzY
    have hzS₀ : z ∈ Subgroup.normalizer (S₀ : Set Ω) := hPn (Subgroup.mem_sup_left hzY)
    have hzSK : z ∈ Subgroup.normalizer ((S₀ ⊓ K : Subgroup Ω) : Set Ω) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hzS₀, hzK⟩
    set BK : Subgroup Ω := Subgroup.normalizer ((S₀ ⊓ K : Subgroup Ω) : Set Ω) ⊓ K with hBKdef
    have hBKMs : ∀ b ∈ BK, b ∈ Ms := fun b hb => hPM ⟨hBK b hb, hL₀H ((le_sup_left : K ≤ K ⊔ C) hb.2)⟩
    have hzBK : ∀ b ∈ BK, z * b * z⁻¹ ∈ BK := by
      intro b hb
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hzK b).mp hb.2⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hzSK hb.1) (Subgroup.inv_mem _ hzSK)
    have hgenBK : ∀ b ∈ BK, z * b * z⁻¹ * b⁻¹ ∈ BK := fun b hb =>
      BK.mul_mem (hzBK b hb) (BK.inv_mem hb)
    have hgenYs : ∀ b ∈ BK, z * b * z⁻¹ * b⁻¹ ∈ Ys := by
      intro b hb
      have e : z * b * z⁻¹ * b⁻¹ = z * (b * z⁻¹ * b⁻¹) := by group
      rw [e]
      exact Ys.mul_mem hzY (hYMn b (hBKMs b hb) z⁻¹ (Ys.inv_mem hzY))
    obtain ⟨W, hWdef⟩ : ∃ W : Subgroup Ω,
        W = Subgroup.closure {w | ∃ b ∈ BK, w = z * b * z⁻¹ * b⁻¹} := ⟨_, rfl⟩
    have hgenW : ∀ b ∈ BK, z * b * z⁻¹ * b⁻¹ ∈ W := fun b hb => by
      rw [hWdef]
      exact Subgroup.subset_closure ⟨b, hb, rfl⟩
    have hWBK : W ≤ BK := by
      rw [hWdef]
      refine (Subgroup.closure_le _).mpr ?_
      rintro w ⟨b, hb, rfl⟩
      exact hgenBK b hb
    have hWYs : W ≤ Ys := by
      rw [hWdef]
      refine (Subgroup.closure_le _).mpr ?_
      rintro w ⟨b, hb, rfl⟩
      exact hgenYs b hb
    have hW2 : IsPGroup 2 ↥W :=
      isPGroup_two_of_no_orderThree a (fun x hx => hpowY x (hWYs hx))
        (fun x hx => hBK3 x (hWBK hx))
    have hWn : ∀ b' ∈ BK, ∀ w ∈ W, b' * w * b'⁻¹ ∈ W := by
      intro b' hb' w hw
      rw [hWdef] at hw
      induction hw using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨b, hb, rfl⟩ := hg
        have e : b' * (z * b * z⁻¹ * b⁻¹) * b'⁻¹ =
            (z * b' * z⁻¹ * b'⁻¹)⁻¹ * (z * (b' * b) * z⁻¹ * (b' * b)⁻¹) := by group
        rw [e]
        exact W.mul_mem (W.inv_mem (hgenW b' hb')) (hgenW (b' * b) (BK.mul_mem hb' hb))
      | one => simp
      | mul x y _ _ ihx ihy => simpa [mul_assoc] using W.mul_mem ihx ihy
      | inv x _ ih => simpa [mul_assoc] using W.inv_mem ih
    have hBKnW : BK ≤ Subgroup.normalizer (W : Set Ω) := by
      intro b' hb'
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨hWn b' hb' w, fun hw => ?_⟩
      have := hWn b'⁻¹ (BK.inv_mem hb') _ hw
      simpa [mul_assoc] using this
    have hSKBK : S₀ ⊓ K ≤ BK := fun s hs => ⟨Subgroup.le_normalizer hs, hs.2⟩
    have hP2 : IsPGroup 2 ↥(S₀ ⊓ K ⊔ W) :=
      IsPGroup.to_sup_of_normal_right' hSK.2.1 hW2 (hSKBK.trans hBKnW)
    have hsupeq : S₀ ⊓ K ⊔ W = S₀ ⊓ K :=
      eq_of_isSylowTwoOf_le hSK le_sup_left (sup_le inf_le_right (hWBK.trans inf_le_right)) hP2
    have hWle : W ≤ S₀ ⊓ K := le_sup_right.trans hsupeq.le
    have hcomm : ∀ b ∈ Subgroup.normalizer ((S₀ ⊓ K : Subgroup Ω) : Set Ω) ⊓ K,
        z * b * z⁻¹ * b⁻¹ ∈ S₀ ⊓ K := fun b hb => hWle (hgenW b hb)
    obtain ⟨x, hxK, hx⟩ := hRig (S₀ ⊓ K) z hSK hzK hzSK hz3 hBK3 hcomm
    have hxBK : x ∈ BK := by
      refine ⟨?_, hxK⟩
      show x ∈ Subgroup.normalizer ((S₀ ⊓ K : Subgroup Ω) : Set Ω)
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        rw [← hx s hs.2]
        exact (Subgroup.mem_normalizer_iff.mp hzSK s).mp hs
      · intro hs
        have hsK : x * s * x⁻¹ ∈ K := hs.2
        have h1 := hx (x⁻¹ * (x * s * x⁻¹) * x) (by
          simpa [mul_assoc] using K.mul_mem (K.mul_mem (K.inv_mem hxK) hsK) hxK)
        have h2 : x * (x⁻¹ * (x * s * x⁻¹) * x) * x⁻¹ = x * s * x⁻¹ := by group
        rw [h2] at h1
        have h3 : s = z⁻¹ * (x * s * x⁻¹) * z := by
          have : z * (x⁻¹ * (x * s * x⁻¹) * x) * z⁻¹ = x * s * x⁻¹ := h1.symm ▸ rfl
          calc s = z⁻¹ * (z * (x⁻¹ * (x * s * x⁻¹) * x) * z⁻¹) * z := by group
            _ = z⁻¹ * (x * s * x⁻¹) * z := by rw [h1]
        rw [h3]
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hzSK) (x * s * x⁻¹)).mp hs
        simpa using this
    have hx3 : ¬ 3 ∣ orderOf x := by
      intro h3
      have hy := orderOf_pow_orderOf_div (orderOf_pos x).ne' h3
      exact hBK3 _ (BK.pow_mem hxBK _) hy
    exact centralizes_of_inner hxK hz3 hx hx3
  have hcent : Ys ≤ Subgroup.centralizer (K : Set Ω) := by
    rw [hYgen]
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨hzY, hz3⟩
    have hz3' : z ^ 3 = 1 := hz3 ▸ pow_orderOf_eq_one z
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro n hn
    have := hz z hzY hz3' n hn
    calc n * z = (z * n * z⁻¹) * z := by rw [this]
      _ = z * n := by group
  have hbot : ⁅K, Ys⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
  rw [hbot] at hKY
  apply hKns
  rw [← hKY]
  infer_instance

end SzN22

end CFSG.Quasithin
