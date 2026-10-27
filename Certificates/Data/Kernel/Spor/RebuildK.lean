module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def rebStep (n w : Nat) (LR TR TRI B : Nat → Nat) (st : Nat × Nat × Bool)
    (l : Nat) : Nat × Nat × Bool :=
  (pcomp n w (mask w) st.1 (TR (roff n (n * w) (LR l) +
      rpos w (mask w) (n * w) (LR l) (pg w (mask w) st.2.1 (B l)))),
    pcomp n w (mask w) (TRI (roff n (n * w) (LR l) +
      rpos w (mask w) (n * w) (LR l) (pg w (mask w) st.2.1 (B l)))) st.2.1,
    st.2.2 && Nat.blt (B l) n &&
      Nat.blt (rpos w (mask w) (n * w) (LR l) (pg w (mask w) st.2.1 (B l))) (rcnt (LR l)))

@[expose] noncomputable def rebK (n w : Nat) (LR TR TRI B : Nat → Nat) (m : Nat) : Nat × Nat × Bool :=
  (List.range m).foldl (rebStep n w LR TR TRI B) (pidn n w, pidn n w, true)

end CFSG.KS.Raw

end
