module

public import CFSG.Quasithin.Background.Harris.Ln2.Basic
public import CFSG.Quasithin.Background.Harris.Ln2.PermRank
public import CFSG.Quasithin.Background.Harris.Ln2.AutRank5
public import CFSG.Quasithin.Background.G116IISL42
public import CFSG.Quasithin.Background.G116IIInputs
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.OneCompActions

public section

namespace CFSG.Quasithin.G11.Harris.Ln2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.Background.Harris.OrdinaryProofs

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem m_le_of_autRank' [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (h : OneCompSetting Γ A L m) {S : Type} [Group S] (e : ↥L ≃* S) {r : ℕ}
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r) : m ≤ r := by
  let ψ' : ↥A →* MulAut S := (MulAut.congr e).toMonoidHom.comp (oneCompConjHom h)
  have hinj' : Function.Injective ψ' :=
    (MulAut.congr e).injective.comp (oneCompConjHom_injective h)
  have hcard : Nat.card ψ'.range = 2 ^ m := by
    rw [← h.A_card]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm
  have hcomm : ∀ x ∈ ψ'.range, ∀ y ∈ ψ'.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact h.A_elem.1.is_comm.comm a b
  have hsq : ∀ x ∈ ψ'.range, x * x = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have := h.A_elem.2 (a : GLV V) a.2
    have h3 : a * a = 1 := Subtype.ext (by simpa [sq] using this)
    rw [h3, map_one]
  have := hr _ hcomm hsq
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

theorem m_le_four [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : OneCompSetting Γ A L m)
    (e : ↥L ≃* CFSG.Quasithin.B42Ln.G4) : m ≤ 4 := by
  obtain ⟨ι⟩ := CFSG.Quasithin.G11.sl42IsoA8
  exact m_le_of_autRank' h e (r := 4) fun B hc h2 =>
    card_le_sixteen_of_mulAut_alt8 ((specialLinearGroupEquivStatedSL 4 (ZMod 2)).trans ι) B hc h2

theorem m_le_seven [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : OneCompSetting Γ A L m)
    (e : ↥L ≃* CFSG.Quasithin.JonesParshall.Curtis.G5) : m ≤ 7 :=
  m_le_of_autRank' h e (r := 7) fun B hc h2 => card_le_128_of_elemAbelian_aut5 B hc h2

end CFSG.Quasithin.G11.Harris.Ln2
